const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const QRCode = require('qrcode');
const WORDS = require('./words');

const PORT = process.env.PORT || 3210;
// En producción (servidor en internet) poner PUBLIC_URL=https://midominio.com
const PUBLIC_URL = (process.env.PUBLIC_URL || '').replace(/\/$/, '');
const ROOM_TTL_MS = 6 * 60 * 60 * 1000;

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
    streams: new Set(),
    touched: Date.now(),
  };
  rooms.set(code, room);
  return room;
}

const spymasterOf = (room, team) => room.players.find((p) => p.team === team && p.role === 'spymaster');
const remaining = (room, team) => room.cards.filter((c) => c.type === team && !c.revealed).length;

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

function startProblem(room) {
  for (const t of TEAMS) {
    if (!spymasterOf(room, t)) return `Falta el jefe de espías del equipo ${TEAM_NAME[t]}`;
    if (!room.players.some((p) => p.team === t && p.role === 'operative')) return `Falta un operativo en el equipo ${TEAM_NAME[t]}`;
  }
  return null;
}

function startGame(room) {
  const first = TEAMS[crypto.randomInt(2)];
  const types = shuffle([
    ...Array(9).fill(first),
    ...Array(8).fill(other(first)),
    ...Array(7).fill('neutral'),
    'assassin',
  ]);
  const words = shuffle([...WORDS]).slice(0, 25);
  room.cards = words.map((word, i) => ({ word, type: types[i], revealed: false }));
  room.state = 'playing';
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
}

function endTurn(room) {
  room.turn = other(room.turn);
  room.phase = 'clue';
  room.clue = null;
  room.guessesLeft = null;
  room.guessesMade = 0;
}

function win(room, team, reason) {
  room.state = 'over';
  room.winner = team;
  room.winReason = reason;
}

function setLast(room, text, type) {
  room.last = { text, type, seq: ++room.lastSeq };
}

// Devuelve un mensaje de error o null si la acción se aplicó.
function act(room, p, a) {
  switch (a.type) {
    case 'setTeam': {
      if (!p) return 'Jugador desconocido';
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
    case 'setAgent': {
      if (!p) return 'Jugador desconocido';
      if (a.agent && !listAgents().includes(a.agent)) return 'Personaje inválido';
      p.agent = a.agent || null;
      return null;
    }
    case 'start': {
      if (room.state !== 'lobby') return 'La partida ya empezó';
      const problem = startProblem(room);
      if (problem) return problem;
      startGame(room);
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
      room.guessesLeft = unlimited ? null : num + 1;
      room.guessesMade = 0;
      room.phase = 'guess';
      return null;
    }
    case 'guess': {
      if (!p || room.state !== 'playing' || room.phase !== 'guess') return 'No es momento de adivinar';
      if (p.team !== room.turn || p.role !== 'operative') return 'No es tu turno';
      const card = Number.isInteger(a.index) ? room.cards[a.index] : null;
      if (!card || card.revealed) return 'Carta inválida';
      card.revealed = true;
      card.agent = teamAgent(room, card.type);
      const team = room.turn;
      room.log.push({ kind: 'guess', team, by: p.name, word: card.word, cardType: card.type });
      if (card.type === 'assassin') {
        setLast(room, `${card.word}: ¡el asesino!`, 'assassin');
        win(room, other(team), 'assassin');
      } else if (card.type === team) {
        setLast(room, `${card.word}: ¡correcto!`, team);
        room.guessesMade++;
        if (remaining(room, team) === 0) win(room, team, 'agents');
        else if (room.guessesLeft !== null && --room.guessesLeft === 0) endTurn(room);
      } else if (card.type === 'neutral') {
        setLast(room, `${card.word}: civil, fin del turno`, 'neutral');
        endTurn(room);
      } else {
        setLast(room, `${card.word}: era del equipo ${TEAM_NAME[card.type]}`, card.type);
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
    case 'abort': {
      if (p) return 'Solo se puede terminar desde la tele';
      if (room.state !== 'playing') return 'No hay partida en curso';
      room.state = 'lobby';
      room.cards = null;
      room.clue = null;
      room.last = null;
      return null;
    }
    case 'newGame': {
      if (room.state !== 'over') return 'La partida no terminó';
      room.state = 'lobby';
      room.cards = null;
      room.clue = null;
      room.last = null;
      return null;
    }
    default:
      return 'Acción desconocida';
  }
}

// Lo que ve cada pantalla. p = null es la tele. Solo los jefes reciben la clave.
function view(room, p) {
  const seesKey = room.state === 'over' || (p && p.role === 'spymaster');
  return {
    code: room.code,
    joinUrl: room.joinUrl,
    agents: listAgents(),
    state: room.state,
    players: room.players.map(({ id, name, team, role, agent, connected }) => ({ id, name, team, role, agent, connected })),
    me: p ? { id: p.id, name: p.name, team: p.team, role: p.role, agent: p.agent } : null,
    startProblem: room.state === 'lobby' ? startProblem(room) : null,
    turn: room.turn,
    phase: room.phase,
    clue: room.clue,
    guessesLeft: room.guessesLeft,
    guessesMade: room.guessesMade,
    winner: room.winner,
    winReason: room.winReason,
    last: room.last,
    log: room.log.slice(-40),
    remaining: room.cards ? { red: remaining(room, 'red'), blue: remaining(room, 'blue') } : null,
    cards: room.cards && room.cards.map((c) => ({
      word: c.word,
      revealed: c.revealed,
      agent: c.revealed ? c.agent || null : null,
      type: c.revealed || seesKey ? c.type : null,
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
        name, team: null, role: null, agent: null, connected: false,
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
