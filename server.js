const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

// Solo se sirve el juego (index.html); así server.js y package.json no quedan expuestos
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));

/* ---------- Salas ---------- */
const MIN_JUGADORES = 2;
const MAX_JUGADORES = 5;
const ALFABETO = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';   // sin 0/O ni 1/I para no confundirse
const MIRADA_MAX_X = 155, MIRADA_MAX_Y = 92;       // zona del ojo por la que puede moverse el iris
const salas = new Map();                               // codigo -> { codigo, max, anfitrion, jugadores }

function nuevoCodigo() {
  let codigo;
  do {
    codigo = Array.from({ length: 5 }, () => ALFABETO[Math.floor(Math.random() * ALFABETO.length)]).join('');
  } while (salas.has(codigo));
  return codigo;
}

// Solo se aceptan datos válidos del perfil del jugador
function limpiarPerfil(p) {
  p = p && typeof p === 'object' ? p : {};
  const hex = /^#[0-9a-f]{6}$/i;
  return {
    nombre: String(p.nombre || '').trim().slice(0, 16) || 'Jugador',
    flama: hex.test(p.flama) ? p.flama : '#df7122',
    saco: hex.test(p.saco) ? p.saco : '#822f00'
  };
}

function estadoSala(sala) {
  return {
    codigo: sala.codigo, max: sala.max, anfitrion: sala.anfitrion, jugadores: sala.jugadores,
    iniciada: !!sala.iniciada, asientos: sala.asientos || 0
  };
}


/* ---------- Juego tipo UNO: cartas, vida, fichas y desafíos ---------- */
// Todo el estado vive en el servidor (sala.juego); los clientes solo piden acciones y dibujan.
// Cada jugador solo ve SU vida: a los demás se les envía null.
const VIDA_INICIAL = 10, FICHAS_INICIALES = 10, FICHAS_POR_RONDA = 1, ANTE = 1;
const MANO_INICIAL = 7;
const META_MONEDAS = 10;                       // gana quien llega a estas monedas espirituales (o el último con vida)
const CURA = 3, PROB_ESCUDO = 0.5;
const BALAS_RULETA = 2;                        // balas de 6 recámaras
const GOLPES_MAX = 15, GOLPES_OK = 2;          // desafío muerte: hasta 2 golpes cuenta como superado
const COLORES = ['r', 'a', 'v', 'y'];          // rojo, azul, verde, amarillo
const ESPECIALES = ['doble', 'escudo', 'ladron', 'cura'];
const MALDITAS = ['ruleta', 'muerte', 'fuego', 'teclas'];
const COPIAS_ESPECIAL = 3, COPIAS_MALDITA = 3;
const DANIO = { ruleta: 5, muerte: 1, fuego: 3, teclas: 3 };   // vida que se pierde (muerte: por golpe)
const DANIO_FALLO = 3;                         // si un jugador no responde a tiempo
const DURACION = { ruleta: 30000, muerte: 15000, fuego: 8000, teclas: 7000 };
const NOMBRES = {
  doble: 'Doble o nada', escudo: 'Escudo', ladron: 'Ladrón', cura: 'Curación',
  ruleta: 'Ruleta rusa', muerte: 'Desafío muerte', fuego: 'Círculo de fuego', teclas: 'Cuchillos'
};

let uidSeq = 0;
function barajar(a) {
  for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}
function crearMazo() {
  const m = [];
  COLORES.forEach(c => { for (let v = 0; v <= 9; v++) { m.push({ t: 'n', c, v }); if (v > 0) m.push({ t: 'n', c, v }); } });
  ESPECIALES.forEach(k => { for (let i = 0; i < COPIAS_ESPECIAL; i++) m.push({ t: 'e', k }); });
  MALDITAS.forEach(k => { for (let i = 0; i < COPIAS_MALDITA; i++) m.push({ t: 'm', k }); });
  m.forEach(c => { c.uid = ++uidSeq; });
  return barajar(m);
}
const nombreDe = (sala, id) => (sala.jugadores.find(j => j.id === id) || {}).nombre || 'Jugador';
const cima = g => g.mesa[g.mesa.length - 1];

function robarCarta(g) {
  if (g.mazo.length === 0) {                      // se rebaraja la mesa (menos la carta de arriba) y los descartes
    const top = g.mesa.pop();
    g.mazo = barajar(g.mesa.concat(g.pozo));
    g.mesa = [top]; g.pozo = [];
  }
  return g.mazo.pop() || null;
}

function iniciarJuego(sala) {
  const orden = sala.jugadores.slice().sort((a, b) => a.asiento - b.asiento).map(j => j.id);
  const jug = {};
  orden.forEach(id => {
    jug[id] = { vida: VIDA_INICIAL, fichas: FICHAS_INICIALES, monedas: 0, mano: [], vivo: true, ante: 0, bono: 0,
                mods: { doble: false, escudo: false, cura: false } };
  });
  sala.juego = { orden, jug, turno: null, fase: 'turno', jugadas: 1, mazo: [], mesa: [], pozo: [], bote: 0, ronda: 0,
                 desafio: null, n: 0, nj: 0, jugada: null, ganador: null, registro: [], ultimo: null, timer: null };
  nuevaRonda(sala, orden[0]);
}

function anotar(sala, txt) {
  const r = sala.juego.registro;
  r.push(txt);
  if (r.length > 8) r.shift();
}

function nuevaRonda(sala, inicia) {
  const g = sala.juego;
  g.ronda++;
  g.mazo = crearMazo(); g.mesa = []; g.pozo = []; g.bote = 0;
  const vivos = g.orden.filter(id => g.jug[id].vivo);
  vivos.forEach(id => {
    const p = g.jug[id];
    if (g.ronda > 1) p.fichas += FICHAS_POR_RONDA;
    p.ante = Math.min(ANTE, p.fichas);             // cada ronda se apuesta una ficha al bote
    p.fichas -= p.ante; g.bote += p.ante;
    p.mods = { doble: false, escudo: false, cura: false }; p.bono = 0;
    p.mano = [];
    for (let i = 0; i < MANO_INICIAL; i++) p.mano.push(g.mazo.pop());
  });
  while (g.mazo.length) {                          // la primera carta de la mesa es siempre un número
    const c = g.mazo.pop();
    if (c.t === 'n') { g.mesa.push(c); break; }
    g.mazo.unshift(c);
  }
  anotar(sala, `Ronda ${g.ronda}: bote de ${g.bote} fichas`);
  empezarTurno(sala, inicia);
}

function empezarTurno(sala, id) {
  const g = sala.juego, p = g.jug[id];
  g.turno = id; g.fase = 'turno'; g.desafio = null;
  g.jugadas = p.bono > 0 ? p.bono : 1;             // la ruleta superada da dos jugadas en tu siguiente turno
  p.bono = 0;
}

function avanzar(sala, desde) {                    // pasa al siguiente jugador vivo a partir de la posición "desde"
  const g = sala.juego, n = g.orden.length;
  for (let k = 0; k < n; k++) {
    const id = g.orden[(desde + k) % n];
    if (g.jug[id].vivo) { empezarTurno(sala, id); return; }
  }
}

function comprobarFin(sala) {
  const g = sala.juego;
  const vivos = g.orden.filter(id => g.jug[id].vivo);
  const meta = g.orden.find(id => g.jug[id].monedas >= META_MONEDAS);
  let fin = false, ganador = null;
  if (meta) { fin = true; ganador = meta; }
  else if (vivos.length <= 1) { fin = true; ganador = vivos[0] || null; }
  if (fin) {
    clearTimeout(g.timer);
    g.fase = 'fin'; g.ganador = ganador; g.turno = null; g.desafio = null;
    if (ganador) anotar(sala, `${nombreDe(sala, ganador)} gana la partida`);
  }
  return fin;
}

// Después de cada jugada: si te quedas sin cartas ganas la ronda; si no, se gasta una jugada y quizá pasa el turno
function trasJugada(sala) {
  const g = sala.juego, id = g.turno, p = g.jug[id];
  if (comprobarFin(sala)) return;
  if (!p.vivo) { avanzar(sala, g.orden.indexOf(id) + 1); return; }
  if (p.mano.length === 0) { ganarRonda(sala, id); return; }
  g.jugadas--;
  if (g.jugadas <= 0) avanzar(sala, g.orden.indexOf(id) + 1);
}

function ganarRonda(sala, id) {
  const g = sala.juego, w = g.jug[id];
  const gana = g.bote * (w.mods.doble ? 2 : 1);
  w.monedas += gana; w.fichas += w.ante;
  g.orden.forEach(o => {                           // quien tenía "Doble o nada" y perdió paga una ficha más
    const p = g.jug[o];
    if (o !== id && p.vivo && p.mods.doble) p.fichas = Math.max(0, p.fichas - 1);
  });
  anotar(sala, `${nombreDe(sala, id)} gana la ronda: +${gana} monedas espirituales`);
  if (comprobarFin(sala)) return;
  const n = g.orden.length, i0 = g.orden.indexOf(id);
  let inicia = id;
  for (let k = 1; k <= n; k++) { const o = g.orden[(i0 + k) % n]; if (g.jug[o].vivo) { inicia = o; break; } }
  nuevaRonda(sala, inicia);                        // empieza el siguiente jugador vivo
}

function iniciarDesafio(sala, tipo, lanzador, objetivo) {
  const g = sala.juego;
  g.n++;
  g.fase = 'desafio';
  const participantes = tipo === 'fuego' ? g.orden.filter(id => g.jug[id].vivo) : [objetivo];   // el fuego es de todos
  const d = { n: g.n, tipo, lanzador, objetivo, participantes, resultados: {}, duracion: DURACION[tipo], bala: null };
  g.desafio = d;
  anotar(sala, tipo === 'fuego'
    ? `${nombreDe(sala, lanzador)} lanza ${NOMBRES[tipo]} a todos`
    : `${nombreDe(sala, lanzador)} lanza ${NOMBRES[tipo]} a ${nombreDe(sala, objetivo)}`);
  clearTimeout(g.timer);
  g.timer = setTimeout(() => {                     // quien no responde a tiempo falla
    if (sala.juego !== g || g.desafio !== d) return;
    if (tipo === 'ruleta') dispararRuleta(sala); else resolverDesafio(sala);
    emitirJuego(sala);
  }, d.duracion + 4000);
}

function dispararRuleta(sala) {
  const d = sala.juego.desafio;
  d.bala = Math.random() < BALAS_RULETA / 6;
  d.resultados[d.objetivo] = { superado: !d.bala, danio: d.bala ? DANIO.ruleta : 0 };
  resolverDesafio(sala);
}

function resolverDesafio(sala) {
  const g = sala.juego, d = g.desafio;
  clearTimeout(g.timer);
  const detalles = [];
  d.participantes.forEach(id => {
    const p = g.jug[id];
    const r = d.resultados[id] || { superado: false, danio: DANIO_FALLO };
    let danio = r.danio, escudo = false, curado = false;
    if (p.mods.escudo) {
      if (danio > 0 && Math.random() < PROB_ESCUDO) { danio = 0; escudo = true; }
      p.mods.escudo = false;
    }
    p.vida -= danio;
    if (p.mods.cura) {
      if (danio === 0) { p.vida = Math.min(VIDA_INICIAL, p.vida + CURA); curado = true; }
      p.mods.cura = false;
    }
    detalles.push({ id, danio, superado: r.superado, escudo, curado });
    if (d.tipo === 'ruleta' && r.superado) {
      p.bono = 2;                                  // gana la oportunidad de tirar dos cartas en su turno
      anotar(sala, `${nombreDe(sala, id)} sobrevive y podrá tirar dos cartas`);
    }
  });
  detalles.forEach(x => {
    const p = g.jug[x.id];
    if (p.vida <= 0) {
      p.vida = 0; p.vivo = false; g.pozo.push(...p.mano); p.mano = [];
      anotar(sala, `${nombreDe(sala, x.id)} ha caído`);
    }
  });
  g.ultimo = { n: d.n, tipo: d.tipo, lanzador: d.lanzador, objetivo: d.objetivo, detalles, bala: d.bala };
  g.desafio = null; g.fase = 'turno';
  trasJugada(sala);
}

function jugadorSale(sala, id) {
  const g = sala.juego;
  const i = g.orden.indexOf(id);
  if (i < 0) return;
  g.pozo.push(...g.jug[id].mano);
  g.orden.splice(i, 1);
  delete g.jug[id];
  if (g.fase === 'fin') { if (g.ganador === id) g.ganador = null; return; }
  if (comprobarFin(sala)) return;
  if (g.fase === 'desafio') {
    const d = g.desafio;
    if (d.lanzador === id || (d.tipo !== 'fuego' && d.objetivo === id)) {   // se cancela el desafío
      clearTimeout(g.timer); g.desafio = null; g.fase = 'turno';
      anotar(sala, 'El desafío se canceló');
      if (g.turno === id) avanzar(sala, i); else trasJugada(sala);
      return;
    }
    d.participantes = d.participantes.filter(x => x !== id);
    delete d.resultados[id];
    if (d.tipo !== 'ruleta' && d.participantes.every(x => d.resultados[x])) resolverDesafio(sala);
    return;
  }
  if (g.turno === id) avanzar(sala, i);
}

// Cada jugador recibe su mano y su vida; de los demás solo se ve cuántas cartas tienen
function vistaJuego(sala, paraId) {
  const g = sala.juego;
  const d = g.desafio, u = g.ultimo;
  return {
    turno: g.turno, fase: g.fase, ganador: g.ganador, meta: META_MONEDAS, vidaMax: VIDA_INICIAL,
    jugada: g.jugada, ronda: g.ronda, bote: g.bote, jugadas: g.jugadas, mesa: g.mesa.length ? cima(g) : null, mazo: g.mazo.length,
    desafio: d ? { n: d.n, tipo: d.tipo, lanzador: d.lanzador, objetivo: d.objetivo, participantes: d.participantes, duracion: d.duracion } : null,
    ultimo: u && {
      n: u.n, tipo: u.tipo, lanzador: u.lanzador, objetivo: u.objetivo, bala: u.bala,
      detalles: u.detalles.map(x => x.id === paraId ? x : { id: x.id, superado: x.superado })   // el daño solo lo ve quien lo recibe
    },
    jugadores: g.orden.map(id => {
      const p = g.jug[id], yo = id === paraId;
      return { id, nombre: nombreDe(sala, id), vida: yo ? p.vida : null, fichas: p.fichas, monedas: p.monedas,
               cartas: p.mano.length, vivo: p.vivo, mods: yo ? p.mods : null };
    }),
    mano: g.jug[paraId] ? g.jug[paraId].mano : [],
    registro: g.registro
  };
}

function emitirJuego(sala) {
  if (!sala.juego) return;
  sala.jugadores.forEach(j => {
    if (sala.juego.jug[j.id]) io.to(j.id).emit('juego', vistaJuego(sala, j.id));
  });
}

function salirDeSala(socket) {
  const codigo = socket.data.sala;
  if (!codigo) return;
  socket.leave(codigo);
  socket.data.sala = null;

  const sala = salas.get(codigo);
  if (!sala) return;
  sala.jugadores = sala.jugadores.filter(j => j.id !== socket.id);

  if (sala.jugadores.length === 0) {
    if (sala.juego) clearTimeout(sala.juego.timer);
    salas.delete(codigo);                                // sala vacía: se elimina
    console.log(`Sala ${codigo} cerrada`);
    return;
  }
  if (sala.juego) jugadorSale(sala, socket.id);
  if (sala.anfitrion === socket.id) sala.anfitrion = sala.jugadores[0].id;   // el siguiente pasa a ser anfitrión
  io.to(codigo).emit('sala', estadoSala(sala));
  emitirJuego(sala);
}

function responder(cb, datos) {
  if (typeof cb === 'function') cb(datos);
}

io.on('connection', (socket) => {
  console.log('Jugador conectado:', socket.id);

  socket.on('crear-sala', (datos, cb) => {
    const max = datos && datos.max;
    if (!Number.isInteger(max) || max < MIN_JUGADORES || max > MAX_JUGADORES) {
      return responder(cb, { ok: false, error: `La sala debe ser de ${MIN_JUGADORES} a ${MAX_JUGADORES} jugadores` });
    }
    salirDeSala(socket);                                 // un jugador solo puede estar en una sala

    const codigo = nuevoCodigo();
    const jugador = { id: socket.id, ...limpiarPerfil(datos.perfil), mirada: { x: 0, y: 0 } };
    const sala = { codigo, max, anfitrion: socket.id, jugadores: [jugador] };
    salas.set(codigo, sala);

    socket.join(codigo);
    socket.data.sala = codigo;
    console.log(`Sala ${codigo} creada (${max} jugadores)`);
    io.to(codigo).emit('sala', estadoSala(sala));
    responder(cb, { ok: true, codigo });
  });

  socket.on('unirse-sala', (datos, cb) => {
    const codigo = String((datos && datos.codigo) || '').trim().toUpperCase();
    const sala = salas.get(codigo);
    if (!sala) return responder(cb, { ok: false, error: 'Esa sala no existe' });

    if (!sala.jugadores.some(j => j.id === socket.id)) {
      if (sala.iniciada) return responder(cb, { ok: false, error: 'La partida ya empezó' });
      if (sala.jugadores.length >= sala.max) return responder(cb, { ok: false, error: 'La sala está llena' });
      salirDeSala(socket);
      sala.jugadores.push({ id: socket.id, ...limpiarPerfil(datos.perfil), mirada: { x: 0, y: 0 } });
      socket.join(codigo);
      socket.data.sala = codigo;
    }
    io.to(codigo).emit('sala', estadoSala(sala));
    responder(cb, { ok: true, codigo });
  });

  // Solo el anfitrión empieza la sala; cada jugador conserva su asiento (un lado de la mesa) hasta el final
  socket.on('iniciar-sala', (datos, cb) => {
    const sala = salas.get(socket.data.sala);
    if (!sala) return responder(cb, { ok: false, error: 'No estás en una sala' });
    if (sala.anfitrion !== socket.id) return responder(cb, { ok: false, error: 'Solo el anfitrión puede empezar' });
    if (sala.iniciada) return responder(cb, { ok: true });
    if (sala.jugadores.length < MIN_JUGADORES) {
      return responder(cb, { ok: false, error: `Se necesitan al menos ${MIN_JUGADORES} jugadores` });
    }
    sala.iniciada = true;
    sala.asientos = sala.jugadores.length;
    sala.jugadores.forEach((j, i) => { j.asiento = i; });
    console.log(`Sala ${sala.codigo} iniciada (${sala.asientos} jugadores)`);
    iniciarJuego(sala);
    io.to(sala.codigo).emit('sala', estadoSala(sala));
    emitirJuego(sala);
    responder(cb, { ok: true });
  });

  // Jugar una carta de tu mano: número (debe coincidir con la mesa), especial o maldita (se lanza a otro jugador)
  socket.on('jugar-carta', (datos, cb) => {
    const sala = salas.get(socket.data.sala);
    const g = sala && sala.juego;
    if (!g || g.fase !== 'turno' || g.turno !== socket.id) return responder(cb, { ok: false, error: 'No es tu turno' });
    const p = g.jug[socket.id];
    const idx = p.mano.findIndex(c => c.uid === (datos && datos.uid));
    if (idx < 0) return responder(cb, { ok: false, error: 'No tienes esa carta' });
    const c = p.mano[idx];
    const yo = nombreDe(sala, socket.id);
    const obj = datos.objetivo, t = g.jug[obj];
    const objetivoValido = t && obj !== socket.id && t.vivo;

    if (c.t === 'n') {
      const top = cima(g);
      if (c.c !== top.c && c.v !== top.v) return responder(cb, { ok: false, error: 'Debe coincidir en color o número' });
      p.mano.splice(idx, 1); g.mesa.push(c);
      g.jugada = { n: ++g.nj, id: socket.id, carta: c, objetivo: null };
      trasJugada(sala);
    } else if (c.t === 'e') {
      if (c.k === 'ladron') {
        if (!objetivoValido || t.mano.length === 0) return responder(cb, { ok: false, error: 'Ese jugador no tiene cartas que robar' });
        p.mano.splice(idx, 1); g.pozo.push(c);
        p.mano.push(t.mano.splice(Math.floor(Math.random() * t.mano.length), 1)[0]);
        g.jugada = { n: ++g.nj, id: socket.id, carta: c, objetivo: obj };
        anotar(sala, `${yo} robó una carta a ${nombreDe(sala, obj)}`);
      } else {
        if (p.mods[c.k]) return responder(cb, { ok: false, error: 'Ese efecto ya está activo' });
        p.mano.splice(idx, 1); g.pozo.push(c);
        p.mods[c.k] = true;
        g.jugada = { n: ++g.nj, id: socket.id, carta: c, objetivo: null };
        anotar(sala, `${yo} usó ${NOMBRES[c.k]}`);                         // la carta se ve en la mesa
      }
      trasJugada(sala);
    } else {
      if (!objetivoValido) return responder(cb, { ok: false, error: 'Elige a quién lanzársela' });
      p.mano.splice(idx, 1); g.pozo.push(c);
      g.jugada = { n: ++g.nj, id: socket.id, carta: c, objetivo: obj };
      iniciarDesafio(sala, c.k, socket.id, obj);                           // trasJugada se llama al resolverlo
    }
    emitirJuego(sala);
    responder(cb, { ok: true });
  });

  // Robar una carta y pasar el turno
  socket.on('robar', (datos, cb) => {
    const sala = salas.get(socket.data.sala);
    const g = sala && sala.juego;
    if (!g || g.fase !== 'turno' || g.turno !== socket.id) return responder(cb, { ok: false, error: 'No es tu turno' });
    const c = robarCarta(g);
    if (c) g.jug[socket.id].mano.push(c);
    anotar(sala, `${nombreDe(sala, socket.id)} robó una carta`);
    if (!comprobarFin(sala)) avanzar(sala, g.orden.indexOf(socket.id) + 1);
    emitirJuego(sala);
    responder(cb, { ok: true });
  });

  // Resultado del desafío de cada participante (muerte: golpes recibidos; fuego y teclas: éxito)
  socket.on('desafio-resultado', (datos) => {
    const sala = salas.get(socket.data.sala);
    const g = sala && sala.juego;
    const d = g && g.desafio;
    if (!d || g.fase !== 'desafio' || d.tipo === 'ruleta') return;
    if (!d.participantes.includes(socket.id) || d.resultados[socket.id]) return;
    let r;
    if (d.tipo === 'muerte') {
      const golpes = Math.max(0, Math.min(GOLPES_MAX, Math.floor(Number(datos && datos.golpes)) || 0));
      r = { superado: golpes <= GOLPES_OK, danio: golpes * DANIO.muerte };
    } else {
      const ok = !!(datos && datos.exito);
      r = { superado: ok, danio: ok ? 0 : DANIO[d.tipo] };
    }
    d.resultados[socket.id] = r;
    if (d.participantes.every(x => d.resultados[x])) { resolverDesafio(sala); emitirJuego(sala); }
  });

  socket.on('ruleta-disparar', () => {
    const sala = salas.get(socket.data.sala);
    const g = sala && sala.juego;
    const d = g && g.desafio;
    if (!d || g.fase !== 'desafio' || d.tipo !== 'ruleta' || d.objetivo !== socket.id) return;
    dispararRuleta(sala);
    emitirJuego(sala);
  });

  // Cada jugador envía hacia dónde mira SU iris; los demás de la sala lo ven en su personaje
  socket.on('mirar', (datos) => {
    const sala = salas.get(socket.data.sala);
    const jugador = sala && sala.jugadores.find(j => j.id === socket.id);
    if (!jugador) return;
    let x = Number(datos && datos.x), y = Number(datos && datos.y);
    if (!Number.isFinite(x) || !Number.isFinite(y)) return;
    const k = Math.hypot(x / MIRADA_MAX_X, y / MIRADA_MAX_Y);   // se mantiene dentro del ojo
    if (k > 1) { x /= k; y /= k; }
    jugador.mirada = { x, y };
    socket.to(sala.codigo).volatile.emit('mira', { id: socket.id, x, y });
  });

  socket.on('salir-sala', () => salirDeSala(socket));

  socket.on('disconnect', () => {
    console.log('Jugador desconectado:', socket.id);
    salirDeSala(socket);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Servidor en http://localhost:${PORT}`);
});