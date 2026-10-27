'use strict';

// ===== 상수 =====
const N = 9;            // 보드 크기
const S = 56;           // 칸 크기
const G = 14;           // 홈(벽 들어가는 틈) 폭
const P = 16;           // 보드 테두리 여백
const STEP = S + G;
const BOARD = N * S + (N - 1) * G + 2 * P;
const WALLS = 10;
const TURN_TIME = 30;   // 초
const AI_DELAY = 500;   // ms
const GOAL = { cat: 0, dog: N - 1 };
const DIRS = [[-1, 0], [1, 0], [0, -1], [0, 1]];
const SVGNS = 'http://www.w3.org/2000/svg';

const other = who => (who === 'cat' ? 'dog' : 'cat');
const key = (r, c) => r * 10 + c;
const idx = p => p.r * N + p.c;
const clamp = (x, lo, hi) => Math.max(lo, Math.min(hi, x));

// ===== 게임 상태 =====
let state;
let orient = 'h';        // 벽 미리보기 방향
let lastLoc = null;      // 마지막 마우스 위치(보드 좌표)
let hover = null;
let deadline = 0;
let timerId = null;
let aiTimer = null;
let resultTimer = null;

function newState() {
  return {
    pawns: { cat: { r: N - 1, c: 4 }, dog: { r: 0, c: 4 } },
    walls: { cat: WALLS, dog: WALLS },
    h: new Set(),          // 가로벽: (r,c) = r행과 r+1행 사이, c·c+1열
    v: new Set(),          // 세로벽: (r,c) = c열과 c+1열 사이, r·r+1행
    placed: [],
    turn: 'cat',
    over: false,
    dogHistory: []
  };
}

// ===== 규칙 =====
function blocked(h, v, r, c, dr, dc) {
  const nr = r + dr, nc = c + dc;
  if (nr < 0 || nr >= N || nc < 0 || nc >= N) return true;
  if (dr === 1) return h.has(key(r, c)) || h.has(key(r, c - 1));
  if (dr === -1) return h.has(key(r - 1, c)) || h.has(key(r - 1, c - 1));
  if (dc === 1) return v.has(key(r, c)) || v.has(key(r - 1, c));
  return v.has(key(r, c - 1)) || v.has(key(r - 1, c - 1));
}

// 목표 줄에서 거꾸로 BFS → 모든 칸의 최단거리 (도달 불가 = Infinity)
function distMap(h, v, goalRow) {
  const d = new Array(N * N).fill(Infinity);
  const q = [];
  for (let c = 0; c < N; c++) {
    d[goalRow * N + c] = 0;
    q.push(goalRow * N + c);
  }
  for (let i = 0; i < q.length; i++) {
    const r = Math.floor(q[i] / N), c = q[i] % N;
    for (const [dr, dc] of DIRS) {
      if (blocked(h, v, r, c, dr, dc)) continue;
      const n = (r + dr) * N + c + dc;
      if (d[n] === Infinity) {
        d[n] = d[q[i]] + 1;
        q.push(n);
      }
    }
  }
  return d;
}

// 겹침·교차·보드 밖 검사
function wallFits(h, v, o, r, c) {
  if (r < 0 || r > N - 2 || c < 0 || c > N - 2) return false;
  if (h.has(key(r, c)) || v.has(key(r, c))) return false;
  if (o === 'h') return !h.has(key(r, c - 1)) && !h.has(key(r, c + 1));
  return !v.has(key(r - 1, c)) && !v.has(key(r + 1, c));
}

// 위 검사 + 두 말 모두 목적지까지 길이 남는지
function wallLegal(st, o, r, c) {
  if (!wallFits(st.h, st.v, o, r, c)) return false;
  const set = o === 'h' ? st.h : st.v;
  set.add(key(r, c));
  const ok = distMap(st.h, st.v, GOAL.cat)[idx(st.pawns.cat)] < Infinity &&
             distMap(st.h, st.v, GOAL.dog)[idx(st.pawns.dog)] < Infinity;
  set.delete(key(r, c));
  return ok;
}

function legalWalls(st) {
  const list = [];
  for (const o of ['h', 'v'])
    for (let r = 0; r < N - 1; r++)
      for (let c = 0; c < N - 1; c++)
        if (wallLegal(st, o, r, c)) list.push({ o, r, c });
  return list;
}

function pawnMoves(st, who) {
  const { h, v } = st;
  const me = st.pawns[who], op = st.pawns[other(who)];
  const res = [];
  for (const [dr, dc] of DIRS) {
    if (blocked(h, v, me.r, me.c, dr, dc)) continue;
    const nr = me.r + dr, nc = me.c + dc;
    if (nr !== op.r || nc !== op.c) {
      res.push({ r: nr, c: nc });
    } else if (!blocked(h, v, nr, nc, dr, dc)) {
      // 점프
      res.push({ r: nr + dr, c: nc + dc });
    } else {
      // 상대 뒤가 막힘 → 대각선
      const sides = dr ? [[0, -1], [0, 1]] : [[-1, 0], [1, 0]];
      for (const [sr, sc] of sides)
        if (!blocked(h, v, nr, nc, sr, sc)) res.push({ r: nr + sr, c: nc + sc });
    }
  }
  return res;
}

// ===== 진행 =====
function movePawn(who, to) {
  state.pawns[who] = { r: to.r, c: to.c };
  if (who === 'dog') {
    state.dogHistory.push(idx(to));
    if (state.dogHistory.length > 6) state.dogHistory.shift();
  }
  if (to.r === GOAL[who]) return finish(who);
  endTurn();
}

function placeWall(who, o, r, c) {
  (o === 'h' ? state.h : state.v).add(key(r, c));
  state.placed.push({ o, r, c, owner: who });
  state.walls[who]--;
  endTurn();
}

function endTurn() {
  state.turn = other(state.turn);
  hover = null;
  if (state.turn === 'dog') {
    stopTimer();
    aiTimer = setTimeout(aiPlay, AI_DELAY);
  } else {
    startTimer();
    refreshHover();
  }
  render();
}

function finish(winner) {
  state.over = true;
  stopTimer();
  hover = null;
  render();
  resultTimer = setTimeout(() => showResult(winner), 450);
}

// 최단경로 쪽으로 한 칸
function bestStep(st, who) {
  const map = distMap(st.h, st.v, GOAL[who]);
  let best = null, bestD = Infinity;
  for (const m of pawnMoves(st, who)) {
    const d = map[idx(m)];
    if (d < bestD) { bestD = d; best = m; }
  }
  return best;
}

// ===== 타이머 =====
function startTimer() {
  stopTimer();
  deadline = Date.now() + TURN_TIME * 1000;
  timerId = setInterval(tick, 100);
  tick();
}

function stopTimer() {
  clearInterval(timerId);
  timerId = null;
}

function tick() {
  const left = Math.max(0, deadline - Date.now());
  renderTimer(left);
  if (left <= 0) onTimeout();
}

function onTimeout() {
  stopTimer();
  if (state.over || state.turn !== 'cat') return;
  if (state.walls.cat > 0) {
    const walls = legalWalls(state);
    if (walls.length) {
      const w = walls[Math.floor(Math.random() * walls.length)];
      return placeWall('cat', w.o, w.r, w.c);
    }
  }
  const step = bestStep(state, 'cat');
  if (step) movePawn('cat', step);
  else endTurn();
}

// ===== AI (최단경로 기반 탐욕) =====
function aiPlay() {
  if (state.over) return;
  const st = state;
  const dogMap = distMap(st.h, st.v, GOAL.dog);
  const catMap = distMap(st.h, st.v, GOAL.cat);
  const myD = dogMap[idx(st.pawns.dog)];
  const opD = catMap[idx(st.pawns.cat)];

  // 1) 가장 좋은 이동 — 최근에 있던 칸은 감점해 왔다 갔다 방지
  let move = null, moveScore = -Infinity;
  for (const m of pawnMoves(st, 'dog')) {
    const d = dogMap[idx(m)];
    let s = d === 0 ? 1000 : -d;
    if (st.dogHistory.includes(idx(m))) s -= 1.5;
    s += Math.random() * 0.1;
    if (s > moveScore) { moveScore = s; move = m; }
  }
  if (move && move.r === GOAL.dog) return movePawn('dog', move);

  // 2) 가장 효과적인 벽 — (상대 경로 증가) - (내 경로 증가)
  let wall = null, wallGain = -Infinity;
  if (st.walls.dog > 0) {
    for (const o of ['h', 'v']) {
      const set = o === 'h' ? st.h : st.v;
      for (let r = 0; r < N - 1; r++) {
        for (let c = 0; c < N - 1; c++) {
          if (!wallFits(st.h, st.v, o, r, c)) continue;
          set.add(key(r, c));
          const nd = distMap(st.h, st.v, GOAL.dog)[idx(st.pawns.dog)];
          const nc = distMap(st.h, st.v, GOAL.cat)[idx(st.pawns.cat)];
          set.delete(key(r, c));
          if (nd === Infinity || nc === Infinity) continue;
          const gain = (nc - opD) - (nd - myD) + Math.random() * 0.1;
          if (gain > wallGain) { wallGain = gain; wall = { o, r, c }; }
        }
      }
    }
  }

  // 이동하면 고양이가 먼저 움직이므로, opD <= myD - 1 이면 경주에서 짐
  const losingRace = opD <= myD - 1;
  const useWall = wall && wallGain >= 1 && (losingRace || wallGain >= 3 || !move);
  if (useWall) return placeWall('dog', wall.o, wall.r, wall.c);
  if (move) return movePawn('dog', move);
  if (wall) return placeWall('dog', wall.o, wall.r, wall.c);
  endTurn();
}

// ===== 그리기 =====
const svg = document.getElementById('board');
const $ = id => document.getElementById(id);

function el(tag, attrs, parent) {
  const e = document.createElementNS(SVGNS, tag);
  for (const k in attrs) e.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(e);
  return e;
}

const cellX = c => P + c * STEP;

svg.setAttribute('viewBox', `0 0 ${BOARD} ${BOARD}`);
el('rect', { x: 0, y: 0, width: BOARD, height: BOARD, rx: 20, class: 'board-bg' }, svg);
const cellLayer = el('g', {}, svg);
for (let r = 0; r < N; r++) {
  for (let c = 0; c < N; c++) {
    const cls = 'cell' + (r === GOAL.cat ? ' goal-cat' : r === GOAL.dog ? ' goal-dog' : '');
    el('rect', { x: cellX(c), y: cellX(r), width: S, height: S, rx: 10, class: cls }, cellLayer);
  }
}
const hintLayer = el('g', {}, svg);
const wallLayer = el('g', {}, svg);
const pawnLayer = el('g', {}, svg);
const previewLayer = el('g', {}, svg);
const pawnEls = {};
for (const who of ['dog', 'cat']) {
  const g = el('g', { class: 'pawn ' + who }, pawnLayer);
  el('use', { href: '#face-' + who, x: 3, y: 3, width: S - 6, height: S - 6 }, g);
  pawnEls[who] = g;
}

function wallRect(w, cls, parent) {
  if (w.o === 'h') {
    el('rect', { x: cellX(w.c), y: cellX(w.r) + S + 2, width: 2 * S + G, height: G - 4, rx: 4, class: cls }, parent);
  } else {
    el('rect', { x: cellX(w.c) + S + 2, y: cellX(w.r), width: G - 4, height: 2 * S + G, rx: 4, class: cls }, parent);
  }
}

function isPlayerTurn() {
  return !state.over && state.turn === 'cat';
}

function render() {
  for (const who of ['cat', 'dog']) {
    const p = state.pawns[who];
    pawnEls[who].style.transform = `translate(${cellX(p.c)}px, ${cellX(p.r)}px)`;
  }

  hintLayer.replaceChildren();
  if (isPlayerTurn()) {
    for (const m of pawnMoves(state, 'cat')) {
      const hot = hover && hover.type === 'cell' && hover.r === m.r && hover.c === m.c;
      el('rect', { x: cellX(m.c) + 3, y: cellX(m.r) + 3, width: S - 6, height: S - 6, rx: 8, class: 'hint-ring' }, hintLayer);
      el('circle', { cx: cellX(m.c) + S / 2, cy: cellX(m.r) + S / 2, r: hot ? 13 : 9, class: 'hint' + (hot ? ' hot' : '') }, hintLayer);
    }
  }

  wallLayer.replaceChildren();
  state.placed.forEach((w, i) => {
    wallRect(w, 'wall ' + w.owner + (i === state.placed.length - 1 ? ' new' : ''), wallLayer);
  });

  previewLayer.replaceChildren();
  if (hover && hover.type === 'wall') wallRect(hover, 'preview ' + (hover.ok ? 'ok' : 'bad'), previewLayer);

  const clickable = hover && (hover.type === 'wall' ? hover.ok : hover.legal);
  svg.style.cursor = clickable ? 'pointer' : 'default';

  // 패널
  const turnCard = $('turnCard');
  turnCard.className = 'card turn ' + state.turn;
  $('turnFace').setAttribute('href', '#face-' + state.turn);
  $('turnText').textContent = state.over ? '게임 종료' : state.turn === 'cat' ? '내 차례' : '멍멍이 차례';

  renderWalls('Cat', state.walls.cat);
  renderWalls('Dog', state.walls.dog);
  if (state.turn === 'dog' || state.over) renderTimer(null);
}

function renderWalls(name, n) {
  const pips = $('pips' + name);
  pips.replaceChildren();
  for (let i = 0; i < WALLS; i++) {
    const s = document.createElement('span');
    if (i >= n) s.className = 'used';
    pips.appendChild(s);
  }
  $('count' + name).textContent = n;
}

function renderTimer(leftMs) {
  const card = $('timerCard');
  if (leftMs === null) {
    card.className = 'card timer paused';
    $('timerText').textContent = state.over ? '—' : '멍멍이 생각 중…';
    $('timerBar').style.width = '100%';
    return;
  }
  card.className = 'card timer' + (leftMs <= 10000 ? ' urgent' : '');
  $('timerText').textContent = Math.ceil(leftMs / 1000) + '초';
  $('timerBar').style.width = (leftMs / (TURN_TIME * 1000) * 100) + '%';
}

function showResult(winner) {
  $('resultFace').setAttribute('href', '#face-' + winner);
  $('resultTitle').textContent = winner === 'cat' ? '승리! 🎉' : '패배…';
  $('resultText').textContent = winner === 'cat'
    ? '고양이가 먼저 도착했어요!'
    : '멍멍이가 먼저 도착했어요. 다시 도전해 보세요!';
  $('result').classList.remove('hidden');
}

// ===== 입력 =====
function locate(evt) {
  const pt = svg.createSVGPoint();
  pt.x = evt.clientX;
  pt.y = evt.clientY;
  const p = pt.matrixTransform(svg.getScreenCTM().inverse());
  const lx = p.x - P, ly = p.y - P;
  const span = N * S + (N - 1) * G;
  if (lx < 0 || ly < 0 || lx >= span || ly >= span) return null;
  const col = Math.floor(lx / STEP), row = Math.floor(ly / STEP);
  const inGap = lx - col * STEP >= S || ly - row * STEP >= S;
  if (inGap) {
    // 가장 가까운 홈 교차점을 벽의 중심으로
    return {
      type: 'wall',
      r: clamp(Math.round((ly + G / 2) / STEP) - 1, 0, N - 2),
      c: clamp(Math.round((lx + G / 2) / STEP) - 1, 0, N - 2)
    };
  }
  return { type: 'cell', r: row, c: col };
}

function refreshHover() {
  hover = null;
  if (!isPlayerTurn() || !lastLoc) return;
  const { r, c } = lastLoc;
  if (lastLoc.type === 'wall') {
    if (state.walls.cat > 0) hover = { type: 'wall', o: orient, r, c, ok: wallLegal(state, orient, r, c) };
  } else {
    const legal = pawnMoves(state, 'cat').some(m => m.r === r && m.c === c);
    hover = { type: 'cell', r, c, legal };
  }
}

svg.addEventListener('mousemove', e => {
  lastLoc = locate(e);
  refreshHover();
  render();
});

svg.addEventListener('mouseleave', () => {
  lastLoc = null;
  refreshHover();
  render();
});

svg.addEventListener('click', e => {
  if (!isPlayerTurn()) return;
  lastLoc = locate(e);
  refreshHover();
  if (!hover) return;
  if (hover.type === 'wall' && hover.ok) placeWall('cat', hover.o, hover.r, hover.c);
  else if (hover.type === 'cell' && hover.legal) movePawn('cat', hover);
});

function toggleOrient() {
  orient = orient === 'h' ? 'v' : 'h';
  refreshHover();
  render();
}

document.addEventListener('contextmenu', e => {
  e.preventDefault();
  toggleOrient();
});

document.addEventListener('keydown', e => {
  if (e.code === 'KeyR' && !e.ctrlKey && !e.metaKey) toggleOrient();
});

function restart() {
  clearTimeout(aiTimer);
  clearTimeout(resultTimer);
  stopTimer();
  state = newState();
  orient = 'h';
  hover = null;
  $('result').classList.add('hidden');
  startTimer();
  refreshHover();
  render();
}

$('restart').addEventListener('click', restart);
$('again').addEventListener('click', restart);

restart();
