const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const QRCode = require('qrcode');
const WORDS = require('./words');
const CATEGORIES = require('./categories');

// De dónde pueden salir las 25 palabras: la lista general, los mazos temáticos y las propias del admin.
const MIX_KEYS = ['random', ...Object.keys(CATEGORIES), 'propias'];
const MIX_LABEL = { random: 'Random', propias: 'Propias' };
for (const key in CATEGORIES) MIX_LABEL[key] = CATEGORIES[key].label;
// Modo dúo: dos jugadores cooperan contra la máquina (turnos limitados y asesinos).
const DUO_WORDS = [4, 5, 6, 7, 8, 9];
const DUO_TURNS = [5, 6, 7, 8, 9, 10, 11, 12];
const DUO_LEVELS = ['facil', 'media', 'dificil'];
const defaultMix = () => Object.fromEntries(MIX_KEYS.map((k) => [k, k === 'random' ? 100 : 0]));

const PORT = process.env.PORT || 3210;
// En producción (servidor en internet) poner PUBLIC_URL=https://midominio.com
const PUBLIC_URL = (process.env.PUBLIC_URL || '').replace(/\/$/, '');
const ROOM_TTL_MS = 6 * 60 * 60 * 1000;
// Las pruebas acortan el segundo para no esperar turnos reales.
const SECOND_MS = Number(process.env.SECOND_MS) || 1000;

const TEAMS = ['red', 'blue'];
const TEAM_NAME = { red: 'ROJO', blue: 'AZUL' };
const other = (t) => (t === 'red' ? 'blue' : 'red');

const rooms = new Map();

// Personajes (public/agents): cada jugador elige uno y aparece en las cartas que acierta.
const AGENTS_DIR = path.join(__dirname, 'public', 'agents');
const AGENT_FILE = /^[\w-]+\.(png|jpe?g|webp)$/i;
const AGENT_MIME = { png: 'image/png', jpg: 'image/jpeg', jpeg: 'image/jpeg', webp: 'image/webp' };
// En la misma carpeta: agente-* son elegibles por los jugadores, civil-* van en las cartas
// neutrales y asesino-* en la carta negra.
function listImages(prefix) {
  try { return fs.readdirSync(AGENTS_DIR).filter((f) => AGENT_FILE.test(f) && f.startsWith(prefix)).sort(); } catch { return []; }
}
const listAgents = () => listImages('agente-');

// ---------- utilidades ----------

function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function newCode() {
  const letters = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
  let code;
  do {
    code = Array.from({ length: 4 }, () => letters[crypto.randomInt(letters.length)]).join('');
  } while (rooms.has(code));
  return code;
}

function lanIp() {
  const all = Object.values(os.networkInterfaces()).flat().filter((i) => i && i.family === 'IPv4' && !i.internal);
  const pref = all.find((i) => /^(192\.168\.|10\.|172\.(1[6-9]|2\d|3[01])\.)/.test(i.address));
  return (pref || all[0] || { address: 'localhost' }).address;
}

function baseUrl(req) {
  if (PUBLIC_URL) return PUBLIC_URL;
  const host = req.headers.host || `localhost:${PORT}`;
  // La tele abre "localhost", pero los celulares necesitan la IP de la red.
  if (/^(localhost|127\.0\.0\.1|\[::1\])(:|$)/.test(host)) return `http://${lanIp()}:${PORT}`;
  const proto = req.headers['x-forwarded-proto'] || 'http';
  return `${proto}://${host}`;
}

const norm = (s) => s.normalize('NFD').replace(/[̀-ͯ]/g, '').toUpperCase().trim();

// ---------- lógica del juego ----------

function createRoom(req) {
  const code = newCode();
  const room = {
    code,
    joinUrl: `${baseUrl(req)}/j/${code}`,
    players: [],
    nextId: 1,
    state: 'lobby', // lobby | playing | over
    cards: null,
    turn: null,
    phase: null, // clue | guess
    clue: null,
    guessesLeft: null, // null = sin límite
    guessesMade: 0,
    winner: null,
    winReason: null,
    last: null,
    lastSeq: 0,
    log: [],
    settings: { turnSeconds: 0, bestOf: 1, customWords: [], mix: defaultMix(), mode: 'teams', duoWords: 7, duoTurns: 9, difficulty: 'facil' },
    duo: null, // estado de la partida en modo dúo
    score: { red: 0, blue: 0 },
    round: 0,
    firstTeam: null,
    seriesOver: false,
    deadline: null,
    timer: null,
    photos: new Map(), // id de jugador -> JPEG de su foto de agente (solo en memoria)
    streams: new Set(),
    touched: Date.now(),
  };
  rooms.set(code, room);
  return room;
}

const spymasterOf = (room, team) => room.players.find((p) => p.team === team && p.role === 'spymaster');
const remaining = (room, team) => room.cards.filter((c) => c.type === team && !c.revealed).length;
// El admin es el primero que entró; si se desconecta, manda el siguiente conectado.
const adminOf = (room) => room.players.find((p) => p.connected) || room.players[0] || null;
const clearPicks = (room) => room.players.forEach((p) => { p.pick = null; });

// Las cartas de un equipo van rotando entre los personajes de ese equipo, empezando por el del jefe.
function teamAgent(room, team) {
  const shown = room.cards.filter((c) => c.type === team && c.revealed).length - 1;
  if (!TEAMS.includes(team)) {
    const images = listImages(team === 'neutral' ? 'civil-' : 'asesino-');
    return images.length ? images[(room.civilOffset + shown) % images.length] : null;
  }
  const members = room.players.filter((p) => p.team === team && p.agent)
    .sort((a, b) => (b.role === 'spymaster') - (a.role === 'spymaster'));
  const pool = [...new Set(members.map((p) => p.agent))];
  if (!pool.length) return null;
  return pool[shown % pool.length];
}

const seatOf = (room, seat) => room.players.find((p) => p.seat === seat);

function startProblem(room) {
  if (room.settings.mode === 'duo') {
    for (const seat of [1, 2]) if (!seatOf(room, seat)) return `Falta el jugador ${seat}`;
    return null;
  }
  for (const t of TEAMS) {
    if (!spymasterOf(room, t)) return `Falta el jefe de espías del equipo ${TEAM_NAME[t]}`;
    if (!room.players.some((p) => p.team === t && p.role === 'operative')) return `Falta un operativo en el equipo ${TEAM_NAME[t]}`;
  }
  return null;
}

function stopTimer(room) {
  clearTimeout(room.timer);
  room.timer = null;
  room.deadline = null;
}

// El reloj cubre el turno entero (pista + adivinar). Al agotarse, el turno pasa al rival.
function armTimer(room, extraSeconds = 0) {
  stopTimer(room);
  const seconds = room.settings.turnSeconds;
  if (room.state !== 'playing' || !seconds) return;
  const ms = (seconds + extraSeconds) * SECOND_MS;
  room.deadline = Date.now() + ms;
  room.timer = setTimeout(() => {
    if (room.state !== 'playing') return;
    setLast(room, room.duo ? '¡Se acabó el tiempo!' : `¡Se acabó el tiempo del equipo ${TEAM_NAME[room.turn]}!`, room.turn, 'time');
    endTurn(room);
    broadcast(room);
  }, ms);
  room.timer.unref();
}

// "PERRO; gato;san martín" -> lista sin repetidos, en mayúsculas.
function parseWords(text) {
  const seen = new Set();
  const out = [];
  for (const raw of String(text || '').slice(0, 10000).split(/[;\n]/)) {
    const word = raw.trim().replace(/\s+/g, ' ').toUpperCase();
    if (!word || word.length > 12 || seen.has(norm(word))) continue;
    seen.add(norm(word));
    out.push(word);
    if (out.length >= 400) break;
  }
  return out;
}

// Reparte las 25 cartas entre los mazos según los porcentajes del admin.
// Si un mazo no alcanza (pocas palabras propias, repetidas), se completa con la lista general.
function pickWords(room) {
  const pools = { random: WORDS, propias: room.settings.customWords };
  for (const key in CATEGORIES) pools[key] = CATEGORIES[key].words;
  const mix = room.settings.mix;
  const keys = MIX_KEYS.filter((k) => mix[k] > 0 && pools[k].length);
  const total = keys.reduce((n, k) => n + mix[k], 0);
  const used = new Set();
  const out = [];
  const take = (pool, n) => {
    for (const word of shuffle([...pool])) {
      if (n <= 0) break;
      if (used.has(norm(word))) continue;
      used.add(norm(word));
      out.push(word);
      n--;
    }
  };
  if (total) {
    // Resto mayor: las cartas que sobran del redondeo van a los mazos con más fracción.
    const shares = keys.map((k) => ({ k, exact: (25 * mix[k]) / total }));
    let spare = 25 - shares.reduce((n, s) => n + Math.floor(s.exact), 0);
    shares.sort((a, b) => (b.exact % 1) - (a.exact % 1));
    for (const s of shares) take(pools[s.k], Math.floor(s.exact) + (spare-- > 0 ? 1 : 0));
  }
  take(WORDS, 25 - out.length);
  return shuffle(out);
}

function startGame(room, first) {
  const types = shuffle([
    ...Array(9).fill(first),
    ...Array(8).fill(other(first)),
    ...Array(7).fill('neutral'),
    'assassin',
  ]);
  room.cards = pickWords(room).map((word, i) => ({ word, type: types[i], revealed: false }));
  room.state = 'playing';
  room.firstTeam = first;
  room.turn = first;
  room.phase = 'clue';
  room.clue = null;
  room.guessesLeft = null;
  room.guessesMade = 0;
  room.winner = null;
  room.winReason = null;
  room.last = null;
  room.log = [];
  room.civilOffset = crypto.randomInt(1000); // para que no empiece siempre el mismo civil
  clearPicks(room);
  // Quien abre tiene una carta más para encontrar: su primer turno dura un minuto extra.
  armTimer(room, 60);
}

function endTurn(room) {
  if (room.duo) return duoEndTurn(room);
  room.turn = other(room.turn);
  room.phase = 'clue';
  room.clue = null;
  room.guessesLeft = null;
  room.guessesMade = 0;
  clearPicks(room);
  armTimer(room);
}

function win(room, team, reason) {
  room.state = 'over';
  room.winner = team;
  room.winReason = reason;
  stopTimer(room);
  clearPicks(room);
  room.score[team]++;
  room.seriesOver = room.score[team] >= Math.ceil(room.settings.bestOf / 2);
}

// ---------- modo dúo ----------
// Cartas: 'p1' las ve el jugador 1 y las adivina el 2; 'p2' al revés.
// 'ass1' la ve el jugador 1 y es mortal para el 2; 'ass2' al revés.

const duoLeft = (room, seat) => room.cards.filter((c) => c.type === 'p' + seat && !c.revealed).length;

function duoPool(difficulty) {
  if (difficulty === 'dificil') return CATEGORIES.abstractas.words;
  if (difficulty === 'media') return Object.keys(CATEGORIES).filter((k) => k !== 'abstractas').flatMap((k) => CATEGORIES[k].words).concat(WORDS);
  return WORDS;
}

// Quien da la pista hace de jefe y el otro adivina: así valen las mismas reglas de turno.
function duoRoles(room) {
  for (const p of room.players) if (p.seat) p.role = p.seat === room.duo.giver ? 'spymaster' : 'operative';
}

function startDuo(room) {
  const n = room.settings.duoWords;
  const types = shuffle([...Array(n).fill('p1'), ...Array(n).fill('p2'), 'ass1', 'ass2', ...Array(23 - 2 * n).fill('neutral')]);
  const used = new Set();
  const words = [];
  for (const word of shuffle([...duoPool(room.settings.difficulty)])) {
    if (words.length === 25) break;
    if (used.has(norm(word))) continue;
    used.add(norm(word));
    words.push(word);
  }
  room.cards = words.map((word, i) => ({ word, type: types[i], revealed: false }));
  room.state = 'playing';
  room.turn = 'blue';
  room.phase = 'clue';
  room.clue = null;
  room.guessesLeft = null;
  room.guessesMade = 0;
  room.winner = null;
  room.winReason = null;
  room.last = null;
  room.log = [];
  room.civilOffset = crypto.randomInt(1000);
  room.duo = { turnNo: 1, giver: 1, result: null };
  duoRoles(room);
  clearPicks(room);
  armTimer(room);
}

function duoFinish(room, result, reason) {
  room.state = 'over';
  room.duo.result = result; // win | lose
  room.winner = result === 'win' ? 'blue' : null;
  room.winReason = reason;  // agents | assassin | turns
  room.seriesOver = true;
  stopTimer(room);
  clearPicks(room);
}

function duoEndTurn(room) {
  const d = room.duo;
  if (d.turnNo >= room.settings.duoTurns) return duoFinish(room, 'lose', 'turns');
  d.turnNo++;
  // Se alternan, salvo que al otro ya no le queden palabras por hacer adivinar.
  const next = d.giver === 1 ? 2 : 1;
  if (duoLeft(room, next) > 0) d.giver = next;
  room.phase = 'clue';
  room.clue = null;
  room.guessesLeft = null;
  room.guessesMade = 0;
  duoRoles(room);
  clearPicks(room);
  armTimer(room);
}

function duoGuess(room, p, card, index) {
  if (card.type === 'p' + p.seat || card.type === 'ass' + p.seat) return 'Esa carta está en tu clave: no es para ti';
  card.revealed = true;
  for (const x of room.players) if (x.pick === index) x.pick = null;
  if (card.type === 'p1' || card.type === 'p2') {
    const pool = [1, 2].map((seat) => seatOf(room, seat)).map((x) => x && x.agent).filter(Boolean);
    const found = room.cards.filter((c) => c.revealed && (c.type === 'p1' || c.type === 'p2')).length - 1;
    card.agent = pool.length ? pool[found % pool.length] : null;
    room.log.push({ kind: 'guess', team: 'blue', by: p.name, word: card.word, cardType: 'blue' });
    setLast(room, `${card.word}: ¡correcto!`, 'blue', 'ok');
    room.guessesMade++;
    if (duoLeft(room, 1) + duoLeft(room, 2) === 0) duoFinish(room, 'win', 'agents');
    else if (duoLeft(room, room.duo.giver) === 0) duoEndTurn(room);
  } else if (card.type === 'neutral') {
    card.agent = teamAgent(room, 'neutral');
    room.log.push({ kind: 'guess', team: 'blue', by: p.name, word: card.word, cardType: 'neutral' });
    setLast(room, `${card.word}: civil, fin del turno`, 'neutral', 'miss');
    duoEndTurn(room);
  } else {
    card.agent = listImages('asesino-')[0] || null;
    room.log.push({ kind: 'guess', team: 'blue', by: p.name, word: card.word, cardType: 'assassin' });
    setLast(room, `${card.word}: ¡el asesino!`, 'assassin', 'assassin');
    duoFinish(room, 'lose', 'assassin');
  }
  return null;
}

// Lo que ve cada quien de una carta en modo dúo: lo revelado y, si juega, su propia clave.
function duoType(room, c, p) {
  const shown = c.type === 'p1' || c.type === 'p2' ? 'blue' : c.type === 'neutral' ? 'neutral' : 'assassin';
  if (c.revealed || room.state === 'over') return shown;
  if (p && p.seat && (c.type === 'p' + p.seat || c.type === 'ass' + p.seat)) return shown;
  return null;
}

function backToLobby(room) {
  if (room.duo) {
    room.duo = null;
    for (const p of room.players) if (p.seat) p.role = p.seat === 1 ? 'spymaster' : 'operative';
  }
  stopTimer(room);
  clearPicks(room);
  room.state = 'lobby';
  room.cards = null;
  room.clue = null;
  room.last = null;
}

// sfx le dice a la tele qué sonido tocar.
function setLast(room, text, type, sfx) {
  room.last = { text, type, sfx, seq: ++room.lastSeq };
}

// Devuelve un mensaje de error o null si la acción se aplicó.
function act(room, p, a) {
  switch (a.type) {
    case 'setTeam': {
      if (!p) return 'Jugador desconocido';
      if (room.settings.mode === 'duo') return 'En modo dúo se elige jugador 1 o jugador 2';
      if (!TEAMS.includes(a.team) || !['spymaster', 'operative'].includes(a.role)) return 'Equipo inválido';
      if (room.state !== 'lobby' && p.team) return 'No puedes cambiar de equipo durante la partida';
      if (a.role === 'spymaster') {
        const boss = spymasterOf(room, a.team);
        if (boss && boss !== p) {
          if (boss.connected || room.state !== 'lobby') return 'Ese equipo ya tiene jefe de espías';
          boss.role = 'operative';
        }
      }
      p.team = a.team;
      p.role = a.role;
      return null;
    }
    case 'setSeat': {
      if (!p) return 'Jugador desconocido';
      if (room.settings.mode !== 'duo') return 'Solo en modo dúo';
      if (room.state !== 'lobby') return 'La partida ya empezó';
      if (a.seat === null) { p.seat = null; p.team = null; p.role = null; return null; }
      if (a.seat !== 1 && a.seat !== 2) return 'Lugar inválido';
      const holder = seatOf(room, a.seat);
      if (holder && holder !== p) {
        if (holder.connected) return 'Ese lugar ya está ocupado';
        holder.seat = null; holder.team = null; holder.role = null;
      }
      p.seat = a.seat;
      p.team = 'blue';
      p.role = a.seat === 1 ? 'spymaster' : 'operative';
      return null;
    }
    case 'setAgent': {
      if (!p) return 'Jugador desconocido';
      if (a.agent && !listAgents().includes(a.agent)) return 'Personaje inválido';
      p.agent = a.agent || null;
      return null;
    }
    case 'start': {
      if (p && adminOf(room) !== p) return 'Solo el admin o la tele pueden empezar';
      if (room.state !== 'lobby') return 'La partida ya empezó';
      const problem = startProblem(room);
      if (problem) return problem;
      room.score = { red: 0, blue: 0 };
      room.round = 1;
      room.seriesOver = false;
      if (room.settings.mode === 'duo') startDuo(room);
      else startGame(room, TEAMS[crypto.randomInt(2)]);
      return null;
    }
    case 'clue': {
      if (!p || room.state !== 'playing' || room.phase !== 'clue') return 'No es momento de dar pista';
      if (p.team !== room.turn || p.role !== 'spymaster') return 'No es tu turno';
      const word = String(a.word || '').trim().toUpperCase();
      if (!word || word.length > 20 || /\s/.test(word)) return 'La pista debe ser una sola palabra';
      if (room.cards.some((c) => !c.revealed && norm(c.word) === norm(word))) return 'La pista no puede ser una palabra del tablero';
      const unlimited = a.num === '∞' || Number(a.num) === 0;
      const num = a.num === '∞' ? '∞' : Number(a.num);
      if (num !== '∞' && !(Number.isInteger(num) && num >= 0 && num <= 9)) return 'Número inválido';
      room.clue = { word, num };
      room.log.push({ kind: 'clue', team: p.team, by: p.name, word, num });
      room.guessesLeft = unlimited || room.duo ? null : num + 1; // en dúo se sigue mientras se acierte
      room.guessesMade = 0;
      room.phase = 'guess';
      return null;
    }
    case 'pick': {
      // Marcar una carta para que el equipo la vea antes de confirmarla.
      if (!p || room.state !== 'playing' || room.phase !== 'guess') return 'No es momento de adivinar';
      if (p.team !== room.turn || p.role !== 'operative') return 'No es tu turno';
      if (a.index === null || a.index === undefined) { p.pick = null; return null; }
      const card = Number.isInteger(a.index) ? room.cards[a.index] : null;
      if (!card || card.revealed) return 'Carta inválida';
      p.pick = a.index;
      return null;
    }
    case 'guess': {
      if (!p || room.state !== 'playing' || room.phase !== 'guess') return 'No es momento de adivinar';
      if (p.team !== room.turn || p.role !== 'operative') return 'No es tu turno';
      const card = Number.isInteger(a.index) ? room.cards[a.index] : null;
      if (!card || card.revealed) return 'Carta inválida';
      if (room.duo) return duoGuess(room, p, card, a.index);
      card.revealed = true;
      card.agent = teamAgent(room, card.type);
      for (const x of room.players) if (x.pick === a.index) x.pick = null;
      const team = room.turn;
      room.log.push({ kind: 'guess', team, by: p.name, word: card.word, cardType: card.type });
      if (card.type === 'assassin') {
        setLast(room, `${card.word}: ¡el asesino!`, 'assassin', 'assassin');
        win(room, other(team), 'assassin');
      } else if (card.type === team) {
        setLast(room, `${card.word}: ¡correcto!`, team, 'ok');
        room.guessesMade++;
        if (remaining(room, team) === 0) win(room, team, 'agents');
        else if (room.guessesLeft !== null && --room.guessesLeft === 0) endTurn(room);
      } else if (card.type === 'neutral') {
        setLast(room, `${card.word}: civil, fin del turno`, 'neutral', 'miss');
        endTurn(room);
      } else {
        setLast(room, `${card.word}: era del equipo ${TEAM_NAME[card.type]}`, card.type, 'enemy');
        if (remaining(room, card.type) === 0) win(room, card.type, 'agents');
        else endTurn(room);
      }
      return null;
    }
    case 'endTurn': {
      if (!p || room.state !== 'playing' || room.phase !== 'guess') return 'No es momento';
      if (p.team !== room.turn || p.role !== 'operative') return 'No es tu turno';
      if (room.guessesMade === 0) return 'Deben elegir al menos una palabra';
      endTurn(room);
      return null;
    }
    case 'takeBoss': {
      // Si el jefe se fue, un operativo de su equipo puede ocupar su lugar.
      if (!p || room.state !== 'playing') return 'No hay partida en curso';
      if (room.duo) return 'En modo dúo no hay jefe que reemplazar';
      if (!p.team || p.role !== 'operative') return 'Solo un operativo puede reemplazar al jefe';
      const boss = spymasterOf(room, p.team);
      if (boss && boss.connected) return 'Tu jefe sigue conectado';
      if (boss) boss.role = 'operative';
      p.role = 'spymaster';
      p.pick = null;
      setLast(room, `${p.name} es el nuevo jefe ${TEAM_NAME[p.team]}`, p.team, 'clue');
      return null;
    }
    case 'kick': {
      if (!p || adminOf(room) !== p) return 'Solo el admin puede expulsar';
      const target = room.players.find((x) => x.id === a.id);
      if (!target || target === p) return 'Jugador inválido';
      room.players = room.players.filter((x) => x !== target);
      for (const st of [...room.streams]) {
        if (st.player === target) { room.streams.delete(st); st.res.end(); }
      }
      return null;
    }
    case 'settings': {
      if (!p || adminOf(room) !== p) return 'Solo el admin cambia los ajustes';
      if (room.state !== 'lobby') return 'Los ajustes se cambian en la sala de espera';
      if (a.turnSeconds !== undefined) {
        if (![0, 60, 90, 120, 180, 240].includes(a.turnSeconds)) return 'Tiempo inválido';
        room.settings.turnSeconds = a.turnSeconds;
      }
      if (a.bestOf !== undefined) {
        if (![1, 3, 5].includes(a.bestOf)) return 'Formato inválido';
        room.settings.bestOf = a.bestOf;
      }
      if (a.mode !== undefined) {
        if (!['teams', 'duo'].includes(a.mode)) return 'Modo inválido';
        if (a.mode !== room.settings.mode) {
          room.settings.mode = a.mode;
          // Cambiar de modo vacía los equipos: los lugares no son los mismos.
          for (const x of room.players) { x.team = null; x.role = null; x.seat = null; }
        }
      }
      if (a.duoWords !== undefined) {
        if (!DUO_WORDS.includes(a.duoWords)) return 'Cantidad de palabras inválida';
        room.settings.duoWords = a.duoWords;
      }
      if (a.duoTurns !== undefined) {
        if (!DUO_TURNS.includes(a.duoTurns)) return 'Cantidad de turnos inválida';
        room.settings.duoTurns = a.duoTurns;
      }
      if (a.difficulty !== undefined) {
        if (!DUO_LEVELS.includes(a.difficulty)) return 'Dificultad inválida';
        room.settings.difficulty = a.difficulty;
      }
      if (a.customWords !== undefined) {
        room.settings.customWords = parseWords(a.customWords);
        // Cargar palabras propias las pone a jugar; borrarlas vuelve a lo anterior.
        const mix = room.settings.mix;
        if (room.settings.customWords.length) { if (!mix.propias) room.settings.mix = { ...defaultMix(), random: 0, propias: 100 }; }
        else { mix.propias = 0; if (!MIX_KEYS.some((k) => mix[k] > 0)) room.settings.mix = defaultMix(); }
      }
      if (a.mix !== undefined) {
        if (!a.mix || typeof a.mix !== 'object') return 'Mezcla inválida';
        const mix = {};
        for (const key of MIX_KEYS) {
          const value = a.mix[key] === undefined ? 0 : a.mix[key];
          if (!Number.isInteger(value) || value < 0 || value > 100) return 'Mezcla inválida';
          mix[key] = value;
        }
        if (!room.settings.customWords.length) mix.propias = 0;
        room.settings.mix = MIX_KEYS.some((k) => mix[k] > 0) ? mix : defaultMix();
      }
      return null;
    }
    case 'abort': {
      if (p && adminOf(room) !== p) return 'Solo el admin o la tele pueden terminar la partida';
      if (room.state !== 'playing') return 'No hay partida en curso';
      backToLobby(room);
      return null;
    }
    case 'next': {
      // Siguiente ronda de la serie: abre el equipo que no abrió la anterior.
      if (p && adminOf(room) !== p) return 'Solo el admin o la tele pueden seguir';
      if (room.state !== 'over' || room.seriesOver) return 'No hay ronda siguiente';
      const problem = startProblem(room);
      if (problem) return problem;
      room.round++;
      startGame(room, other(room.firstTeam));
      return null;
    }
    case 'newGame': {
      if (p && adminOf(room) !== p) return 'Solo el admin o la tele pueden volver a la sala';
      if (room.state !== 'over') return 'La partida no terminó';
      backToLobby(room);
      return null;
    }
    default:
      return 'Acción desconocida';
  }
}

// Lo que ve cada pantalla. p = null es la tele. Solo los jefes reciben la clave.
function view(room, p) {
  const seesKey = room.state === 'over' || (p && p.role === 'spymaster');
  const admin = adminOf(room);
  const myBoss = p && p.team ? spymasterOf(room, p.team) : null;
  const guessing = room.state === 'playing' && room.phase === 'guess';
  return {
    code: room.code,
    joinUrl: room.joinUrl,
    agents: listAgents(),
    state: room.state,
    players: room.players.map(({ id, name, team, role, seat, agent, connected }) => ({ id, name, team, role, seat, agent, connected })),
    adminId: admin ? admin.id : null,
    me: p ? {
      id: p.id, name: p.name, team: p.team, role: p.role, seat: p.seat, agent: p.agent,
      isAdmin: admin === p,
      canTakeBoss: room.state === 'playing' && !room.duo && !!p.team && p.role === 'operative' && (!myBoss || !myBoss.connected),
      customText: admin === p ? room.settings.customWords.join('; ') : undefined,
    } : null,
    settings: { turnSeconds: room.settings.turnSeconds, bestOf: room.settings.bestOf, customCount: room.settings.customWords.length, mix: room.settings.mix,
      mode: room.settings.mode, duoWords: room.settings.duoWords, duoTurns: room.settings.duoTurns, difficulty: room.settings.difficulty },
    duo: room.duo && room.cards ? { turnNo: room.duo.turnNo, maxTurns: room.settings.duoTurns, giver: room.duo.giver, result: room.duo.result, left1: duoLeft(room, 1), left2: duoLeft(room, 2) } : null,
    mixOptions: MIX_KEYS.map((id) => ({ id, label: MIX_LABEL[id] })),
    score: room.score,
    round: room.round,
    seriesOver: room.seriesOver,
    startProblem: room.state === 'lobby' ? startProblem(room) : null,
    turn: room.turn,
    phase: room.phase,
    clue: room.clue,
    guessesLeft: room.guessesLeft,
    guessesMade: room.guessesMade,
    deadline: room.deadline,
    now: Date.now(), // para que cada pantalla corrija la diferencia con su propio reloj
    picks: guessing ? room.players.filter((x) => x.team === room.turn && Number.isInteger(x.pick)).map((x) => ({ id: x.id, index: x.pick })) : [],
    winner: room.winner,
    winReason: room.winReason,
    last: room.last,
    log: room.log.slice(-40),
    remaining: !room.cards ? null : room.duo ? { red: 0, blue: duoLeft(room, 1) + duoLeft(room, 2) } : { red: remaining(room, 'red'), blue: remaining(room, 'blue') },
    cards: room.cards && room.cards.map((c) => ({
      word: c.word,
      revealed: c.revealed,
      agent: c.revealed ? c.agent || null : null,
      type: room.duo ? duoType(room, c, p) : c.revealed || seesKey ? c.type : null,
    })),
  };
}

function broadcast(room) {
  room.touched = Date.now();
  for (const s of room.streams) {
    s.res.write(`data: ${JSON.stringify(view(room, s.player))}\n\n`);
  }
}

// ---------- servidor HTTP ----------

function sendJson(res, status, obj) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}

function sendFile(res, name) {
  fs.readFile(path.join(__dirname, 'public', name), (err, data) => {
    if (err) return sendJson(res, 404, { error: 'No encontrado' });
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end(data);
  });
}

// Cuerpo binario con tope de tamaño (fotos de agente). Devuelve null si se pasa.
function readRaw(req, limit) {
  return new Promise((resolve) => {
    const chunks = [];
    let size = 0;
    req.on('data', (d) => {
      size += d.length;
      if (size > limit) { resolve(null); req.destroy(); } else chunks.push(d);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', () => resolve(null));
  });
}

function readBody(req) {
  return new Promise((resolve) => {
    let raw = '';
    req.on('data', (d) => {
      raw += d;
      if (raw.length > 10000) req.destroy();
    });
    req.on('end', () => {
      try {
        const body = JSON.parse(raw || '{}');
        resolve(body && typeof body === 'object' && !Array.isArray(body) ? body : {});
      } catch { resolve({}); }
    });
  });
}

async function handle(req, res) {
  const url = new URL(req.url, 'http://x');
  const p = url.pathname;

  if (req.method === 'GET' && p === '/') return sendFile(res, 'tv.html');
  if (req.method === 'GET' && /^\/j\/[A-Za-z]{4}$/.test(p)) return sendFile(res, 'play.html');

  if (req.method === 'GET' && p.startsWith('/agents/')) {
    const name = p.slice('/agents/'.length);
    if (!AGENT_FILE.test(name)) return sendJson(res, 404, { error: 'No encontrado' });
    return fs.readFile(path.join(AGENTS_DIR, name), (err, data) => {
      if (err) return sendJson(res, 404, { error: 'No encontrado' });
      res.writeHead(200, { 'Content-Type': AGENT_MIME[name.split('.').pop().toLowerCase()], 'Cache-Control': 'public, max-age=3600' });
      res.end(data);
    });
  }

  // Foto sacada con la cámara del celular: se guarda en la sala y pasa a ser el personaje del jugador.
  if (req.method === 'POST' && p === '/api/photo') {
    const room = rooms.get((url.searchParams.get('room') || '').toUpperCase());
    const player = room && room.players.find((x) => x.token === url.searchParams.get('token'));
    if (!player) return sendJson(res, 404, { error: 'Jugador desconocido' });
    const jpeg = await readRaw(req, 300000);
    if (!jpeg) return sendJson(res, 413, { error: 'La foto es demasiado grande' });
    if (jpeg.length < 100 || jpeg[0] !== 0xff || jpeg[1] !== 0xd8 || jpeg[2] !== 0xff) return sendJson(res, 400, { error: 'La foto no es válida' });
    room.photos.set(player.id, jpeg);
    player.photoVersion = (player.photoVersion || 0) + 1;
    player.agent = `foto:${player.id}:${player.photoVersion}`;
    broadcast(room);
    return sendJson(res, 200, { ok: true });
  }

  if (req.method === 'GET' && p.startsWith('/photo/')) {
    const [, , roomCode, id] = p.split('/');
    const room = rooms.get(String(roomCode || '').toUpperCase());
    const jpeg = room && room.photos.get(Number(id));
    if (!jpeg) return sendJson(res, 404, { error: 'No encontrado' });
    res.writeHead(200, { 'Content-Type': 'image/jpeg', 'Cache-Control': 'private, max-age=3600' });
    return res.end(jpeg);
  }

  if (req.method === 'GET' && p === '/qr') {
    const room = rooms.get((url.searchParams.get('room') || '').toUpperCase());
    if (!room) return sendJson(res, 404, { error: 'Sala no encontrada' });
    const svg = await QRCode.toString(room.joinUrl, { type: 'svg', margin: 1, errorCorrectionLevel: 'M' });
    res.writeHead(200, { 'Content-Type': 'image/svg+xml', 'Cache-Control': 'no-store' });
    return res.end(svg);
  }

  // La tele crea la sala (o recupera la suya si recarga).
  if (req.method === 'POST' && p === '/api/room') {
    const body = await readBody(req);
    const room = rooms.get(String(body.code || '').toUpperCase()) || createRoom(req);
    return sendJson(res, 200, { code: room.code });
  }

  if (req.method === 'GET' && p === '/api/events') {
    const room = rooms.get((url.searchParams.get('room') || '').toUpperCase());
    if (!room) return sendJson(res, 404, { error: 'Sala no encontrada' });
    const token = url.searchParams.get('token');
    const player = token ? room.players.find((x) => x.token === token) : null;
    if (token && !player) return sendJson(res, 404, { error: 'Jugador desconocido' });
    res.writeHead(200, {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-store',
      Connection: 'keep-alive',
      'X-Accel-Buffering': 'no',
    });
    const stream = { res, player };
    room.streams.add(stream);
    if (player) player.connected = true;
    broadcast(room);
    const ping = setInterval(() => res.write(': ping\n\n'), 20000);
    req.on('close', () => {
      clearInterval(ping);
      room.streams.delete(stream);
      if (player && ![...room.streams].some((s) => s.player === player)) {
        player.connected = false;
        broadcast(room);
      }
    });
    return;
  }

  if (req.method === 'POST' && p === '/api/action') {
    const a = await readBody(req);
    const room = rooms.get(String(a.room || '').toUpperCase());
    if (!room) return sendJson(res, 404, { error: 'La sala no existe' });

    if (a.type === 'join') {
      const name = String(a.name || '').trim().slice(0, 14);
      if (!name) return sendJson(res, 400, { error: 'Escribe tu nombre' });
      if (room.players.length >= 20) return sendJson(res, 400, { error: 'La sala está llena' });
      const player = {
        id: room.nextId++,
        token: crypto.randomBytes(12).toString('hex'),
        name, team: null, role: null, seat: null, agent: null, pick: null, connected: false,
      };
      room.players.push(player);
      broadcast(room);
      return sendJson(res, 200, { token: player.token });
    }

    const player = a.token ? room.players.find((x) => x.token === a.token) : null;
    if (a.token && !player) return sendJson(res, 404, { error: 'Jugador desconocido' });
    if (a.type === 'hello') return sendJson(res, 200, { ok: true });

    const error = act(room, player, a);
    if (error) return sendJson(res, 400, { error });
    broadcast(room);
    return sendJson(res, 200, { ok: true });
  }

  sendJson(res, 404, { error: 'No encontrado' });
}

// Un error en una petición no debe tirar abajo las partidas en curso.
const server = http.createServer((req, res) => {
  handle(req, res).catch((err) => {
    console.error(err);
    if (res.headersSent) res.end();
    else sendJson(res, 500, { error: 'Error del servidor' });
  });
});

setInterval(() => {
  for (const [code, room] of rooms) {
    if (room.streams.size === 0 && Date.now() - room.touched > ROOM_TTL_MS) rooms.delete(code);
  }
}, 10 * 60 * 1000).unref();

server.listen(PORT, () => {
  console.log(`Pantalla de la tele:  http://localhost:${PORT}`);
  console.log(`Los celulares entran: ${PUBLIC_URL || `http://${lanIp()}:${PORT}`}/j/<código>`);
});
