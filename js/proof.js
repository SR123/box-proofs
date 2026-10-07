// The proof model used by the editor: a partial Fitch-style box proof.
//
// A proof is a list of items.  An item is a line or a box:
//   { k: 'line', id, f, rule, refs }   rule === null means an open goal
//   { k: 'box', id, items }            items[0] is the assumption line
// refs are ids of lines (or of boxes, for rules that close boxes).
// Open goals are shown with a vertical-dots gap above them, as on the
// lecture slides about working backwards.

import { BOT, imp, not, show } from './formula.js';
import { rulesOf } from './games.js';

export const RULE_NAME = {
  premise: 'premise', assumption: 'assumption', copy: 'line',
  andI: '∧ intro', andE: '∧ elim', impI: '→ intro', impE: '→ elim',
  notI: '¬ intro', notE: '¬ elim', orI: '∨ intro', orE: '∨ elim',
  contra: 'contra', raa: 'contra (classical)', iffI: '↔ intro', iffE: '↔ elim',
};

// Rules that close a box (the box must be immediately above the line).
export const BOX_RULES = new Set(['impI', 'notI', 'raa', 'orE']);

function mkLine(p, f, rule, refs = []) {
  return { k: 'line', id: p.nextId++, f, rule, refs };
}
function mkBox(p, items) {
  return { k: 'box', id: p.nextId++, items };
}

export function newProof(premises, goal) {
  const p = { premises: premises.slice(), goal, items: [], nextId: 1 };
  for (const f of premises) p.items.push(mkLine(p, f, 'premise'));
  p.items.push(mkLine(p, goal, null));
  autoClose(p);
  clearNewest(p);
  return p;
}

function cloneItems(items) {
  return items.map((it) => (it.k === 'line'
    ? { k: 'line', id: it.id, f: it.f, rule: it.rule, refs: it.refs.slice(), newest: it.newest || undefined, anc: it.anc }
    : { k: 'box', id: it.id, items: cloneItems(it.items), newest: it.newest || undefined }));
}

export function cloneProof(p) {
  return { premises: p.premises.slice(), goal: p.goal, items: cloneItems(p.items), nextId: p.nextId };
}

export function forEachItem(p, fn) {
  const rec = (items, depth) => {
    for (const it of items) {
      fn(it, depth);
      if (it.k === 'box') rec(it.items, depth + 1);
    }
  };
  rec(p.items, 0);
}

function clearNewest(p) {
  forEachItem(p, (it) => { delete it.newest; });
}

// Find an item; returns { item, items, index, chain } where chain lists, for
// every level from the top, the block (items array) and the index of the
// element on the way to the item.
export function locate(p, id) {
  const chain = [];
  const rec = (items) => {
    for (let i = 0; i < items.length; i++) {
      const it = items[i];
      if (it.id === id) { chain.push({ items, index: i }); return it; }
      if (it.k === 'box') {
        chain.push({ items, index: i });
        const r = rec(it.items);
        if (r) return r;
        chain.pop();
      }
    }
    return null;
  };
  const item = rec(p.items);
  if (!item) return null;
  const last = chain[chain.length - 1];
  return { item, items: last.items, index: last.index, chain };
}

// Justified lines that may be used at the position of item id
// (above it, and not inside a box that has already been closed).
export function visibleLines(p, id) {
  const loc = typeof id === 'object' ? id : locate(p, id);
  const out = [];
  for (const { items, index } of loc.chain) {
    for (let i = 0; i < index; i++) {
      const it = items[i];
      if (it.k === 'line' && it.rule !== null) out.push(it);
    }
  }
  return out;
}

export function openGoals(p) {
  const out = [];
  forEachItem(p, (it) => { if (it.k === 'line' && it.rule === null) out.push(it); });
  return out;
}

export const isComplete = (p) => openGoals(p).length === 0;

export function numbering(p) {
  const num = new Map();
  const range = new Map();
  let n = 0;
  const rec = (items) => {
    for (const it of items) {
      if (it.k === 'line') num.set(it.id, ++n);
      else {
        const a = n + 1;
        rec(it.items);
        range.set(it.id, [a, n]);
      }
    }
  };
  rec(p.items);
  return { num, range, count: n };
}

const DASH = '–';

export function refText(ref, nb) {
  if (nb.num.has(ref)) return String(nb.num.get(ref));
  const r = nb.range.get(ref);
  return r ? `${r[0]}${DASH}${r[1]}` : '?';
}

export function justificationText(line, nb) {
  if (line.rule === null) return '';
  if (line.rule === 'premise' || line.rule === 'assumption') return line.rule;
  const refs = line.refs.map((r) => refText(r, nb)).join(',');
  return `${RULE_NAME[line.rule]} ${refs}`;
}

// Rows for display: gap rows (open goals) and line rows, plus box extents.
export function layoutRows(p) {
  const nb = numbering(p);
  const rows = [];
  const boxes = [];
  const rec = (items, depth, boxPath) => {
    for (const it of items) {
      if (it.k === 'line') {
        if (it.rule === null) rows.push({ kind: 'gap', goalId: it.id, depth, boxPath });
        rows.push({ kind: 'line', line: it, num: nb.num.get(it.id), depth, boxPath });
      } else {
        const start = rows.length;
        rec(it.items, depth + 1, [...boxPath, it.id]);
        boxes.push({ id: it.id, depth: depth + 1, startRow: start, endRow: rows.length - 1, newest: !!it.newest });
      }
    }
  };
  rec(p.items, 0, []);
  return { rows, boxes, nb };
}

// Ids of the lines a justification uses, with boxes expanded to all their lines.
export function referencedLineIds(p, line) {
  const out = [];
  for (const r of line.refs) {
    const loc = locate(p, r);
    if (!loc) continue;
    if (loc.item.k === 'line') out.push(r);
    else {
      const rec = (items) => { for (const it of items) { if (it.k === 'line') out.push(it.id); else rec(it.items); } };
      rec(loc.item.items);
    }
  }
  return out;
}

// Flat form used by the checker and the exporters.
// Each line: { num, depth, f, rule, refs: [number | [a, b]] }.
export function toFlat(p) {
  const nb = numbering(p);
  const out = [];
  const rec = (items, depth) => {
    for (const it of items) {
      if (it.k === 'line') {
        out.push({
          num: nb.num.get(it.id), depth, f: it.f, rule: it.rule, id: it.id,
          refs: it.refs.map((r) => (nb.num.has(r) ? nb.num.get(r) : nb.range.get(r) || null)),
        });
      } else rec(it.items, depth + 1);
    }
  };
  rec(p.items, 0);
  return out;
}

// Build a model from flat lines (for imported proofs that passed the checker).
export function fromFlat(premises, goal, flat) {
  const p = { premises: premises.slice(), goal, items: [], nextId: 1 };
  const stack = [{ items: p.items, box: null }];
  const lineId = [];
  const boxes = []; // { box, start, end }
  const open = [];
  flat.forEach((l, i) => {
    const n = i + 1;
    if (l.rule === 'assumption') {
      while (stack.length > 1 && stack.length - 1 >= l.depth) {
        stack.pop();
        open.pop().end = n - 1;
      }
      const box = mkBox(p, []);
      stack[stack.length - 1].items.push(box);
      stack.push({ items: box.items, box });
      const rec = { box, start: n, end: null };
      boxes.push(rec);
      open.push(rec);
    } else {
      while (stack.length - 1 > l.depth) {
        stack.pop();
        open.pop().end = n - 1;
      }
    }
    const line = mkLine(p, l.f, l.rule, []);
    line._refs = l.refs;
    stack[stack.length - 1].items.push(line);
    lineId[n] = line.id;
  });
  while (open.length) open.pop().end = flat.length;
  const boxSlots = { impI: [0], notI: [0], raa: [0], orE: [1, 2] };
  forEachItem(p, (it) => {
    if (it.k !== 'line' || !it._refs) return;
    it.refs = it._refs.map((r0, j) => {
      const r = !Array.isArray(r0) && (boxSlots[it.rule] || []).includes(j) ? [r0, r0] : r0;
      if (Array.isArray(r)) {
        if (!(boxSlots[it.rule] || []).includes(j) && r[0] === r[1]) return lineId[r[0]] ?? -1;
        const b = boxes.find((x) => x.start === r[0] && x.end === r[1]);
        return b ? b.box.id : -1;
      }
      return lineId[r] ?? -1;
    });
    delete it._refs;
  });
  return p;
}

// ---------------------------------------------------------------------------
// Closing goals automatically.
//
// A goal is closed when its formula is identical to a line visible from it.
// A goal that is not the last line of its box (for instance one half of an
// ∧ intro) is closed by pointing its uses at that line.  A goal that must be
// the last line of its box (or the conclusion) is merged with the line just
// above it when that line has the same formula, and otherwise becomes a copy
// "line k".

function redirect(p, from, to) {
  forEachItem(p, (it) => {
    if (it.k === 'line') it.refs = it.refs.map((r) => (r === from ? to : r));
  });
}

export function autoClose(p) {
  for (let guard = 0; guard < 1000; guard++) {
    let changed = false;
    for (const g of openGoals(p)) {
      const loc = locate(p, g.id);
      const vis = visibleLines(p, loc);
      let m = null;
      for (let j = vis.length - 1; j >= 0; j--) if (vis[j].f === g.f) { m = vis[j]; break; }
      if (!m) continue;
      const lastInBlock = loc.index === loc.items.length - 1;
      if (lastInBlock) {
        const prev = loc.items[loc.index - 1];
        if (prev && prev.k === 'line' && prev.rule !== null && prev.f === g.f) {
          loc.items.splice(loc.index, 1);
          redirect(p, g.id, prev.id);
        } else {
          g.rule = 'copy';
          g.refs = [m.id];
          g.newest = true;
        }
      } else {
        loc.items.splice(loc.index, 1);
        redirect(p, g.id, m.id);
      }
      changed = true;
      break;
    }
    if (!changed) return;
  }
}

// ---------------------------------------------------------------------------
// Moves.
//
// Backward moves act on an open goal; forward moves use lines visible from
// the goal and insert new lines just above it.
//
//   andI impI notI iffI raa contra       { type, goalId }
//   orI                                  { type, goalId, side: 'left'|'right' }
//   andE iffE                            { type, goalId, lines: [k], side }
//   impE                                 { type, goalId, lines: [x, xy] }
//   impEG  (antecedent becomes a goal)   { type, goalId, lines: [xy] }
//   notE                                 { type, goalId, lines: [a, na] }
//   notEG  (A becomes a goal, gives ⊥)   { type, goalId, lines: [na] }
//   orE                                  { type, goalId, lines: [k] }

export const BACKWARD = new Set(['andI', 'impI', 'notI', 'iffI', 'orI', 'contra', 'raa']);

export const moveKey = (m) => `${m.type}:${m.goalId}:${(m.lines || []).join(',')}:${m.side || ''}`;

// The formula a forward move adds, or the new goal of a backward move.
export function moveResult(p, m) {
  const g = locate(p, m.goalId).item;
  const L = (m.lines || []).map((id) => locate(p, id).item.f);
  switch (m.type) {
    case 'andE': return m.side === 'left' ? L[0].a : L[0].b;
    case 'iffE': return m.side === 'left' ? imp(L[0].a, L[0].b) : imp(L[0].b, L[0].a);
    case 'impE': return L[1].b;
    case 'impEG': return L[0].b;
    case 'notE': case 'notEG': return BOT;
    case 'orI': return m.side === 'left' ? g.f.a : g.f.b;
    default: return g.f;
  }
}

export function listMoves(p, goalId, game) {
  const R = rulesOf(game);
  const loc = locate(p, goalId);
  if (!loc || loc.item.k !== 'line' || loc.item.rule !== null) return [];
  const G = loc.item.f;
  const vis = visibleLines(p, loc);
  // One line per formula: the first visible occurrence.
  const byF = new Map();
  for (const l of vis) if (!byF.has(l.f)) byF.set(l.f, l);
  const has = (f) => byF.has(f);
  const moves = [];
  const back = (type, extra = {}) => moves.push({ type, dir: 'back', goalId, ...extra });
  const fwd = (type, lines, extra = {}) => moves.push({ type, dir: 'fwd', goalId, lines, ...extra });

  if (G.t === 'imp' && R.has('impI')) back('impI');
  if (G.t === 'and' && R.has('andI')) back('andI');
  if (G.t === 'not' && R.has('notI')) back('notI');
  if (G.t === 'iff' && R.has('iffI')) back('iffI');
  if (G.t === 'or' && R.has('orI')) {
    back('orI', { side: 'left' });
    if (G.a !== G.b) back('orI', { side: 'right' });
  }
  if (G !== BOT && R.has('contra')) back('contra');
  if (G !== BOT && R.has('raa')) back('raa');

  for (const [f, l] of byF) {
    switch (f.t) {
      case 'and':
        if (R.has('andE')) {
          if (!has(f.a)) fwd('andE', [l.id], { side: 'left' });
          if (f.b !== f.a && !has(f.b)) fwd('andE', [l.id], { side: 'right' });
        }
        break;
      case 'iff':
        if (R.has('iffE')) {
          if (!has(imp(f.a, f.b))) fwd('iffE', [l.id], { side: 'left' });
          if (f.a !== f.b && !has(imp(f.b, f.a))) fwd('iffE', [l.id], { side: 'right' });
        }
        break;
      case 'imp':
        if (R.has('impE') && !has(f.b)) {
          if (has(f.a)) fwd('impE', [byF.get(f.a).id, l.id]);
          else if (f.a !== G) fwd('impEG', [l.id]); // not "to prove X, first prove X"
        }
        break;
      case 'not':
        if (R.has('notE') && !has(BOT)) {
          if (has(f.a)) fwd('notE', [byF.get(f.a).id, l.id]);
          else if (G === BOT && f.a !== BOT) fwd('notEG', [l.id]);
        }
        break;
      case 'or':
        if (R.has('orE') && !has(f.a) && !has(f.b)) fwd('orE', [l.id]);
        break;
      default:
        break;
    }
  }
  return moves;
}

// Apply a move.  Returns { proof, newGoals } and never changes p0.
export function applyMove(p0, m) {
  const p = cloneProof(p0);
  clearNewest(p);
  const loc = locate(p, m.goalId);
  if (!loc || loc.item.k !== 'line' || loc.item.rule !== null) throw new Error('That goal is not open.');
  const g = loc.item;
  const G = g.f;
  const newGoals = [];
  // Each new goal remembers the situations (available formulas, goal) it
  // came from, so that the guide can spot moves that go round in a circle.
  const anc = [...(g.anc || []), { ctx: contextOf(p0, m.goalId), goal: G }];
  const insert = (...items) => {
    loc.items.splice(loc.index, 0, ...items);
    loc.index += items.length;
  };
  const goal = (f) => {
    const l = mkLine(p, f, null);
    l.newest = true;
    l.anc = anc;
    newGoals.push(l.id);
    return l;
  };
  const line = (f, rule, refs) => {
    const l = mkLine(p, f, rule, refs);
    l.newest = true;
    return l;
  };
  const lineAt = (id) => {
    const l = locate(p, id);
    if (!l) throw new Error('Unknown line.');
    return l.item;
  };
  const justify = (rule, refs) => {
    g.rule = rule;
    g.refs = refs;
    g.newest = true;
  };
  const boxWith = (assumption, target) => {
    const a = line(assumption, 'assumption', []);
    const t = goal(target);
    const b = mkBox(p, [a, t]);
    b.newest = true;
    return b;
  };

  switch (m.type) {
    case 'andI':
    case 'iffI': {
      const X = m.type === 'andI' ? G.a : imp(G.a, G.b);
      const Y = m.type === 'andI' ? G.b : imp(G.b, G.a);
      const gx = goal(X);
      if (X === Y) {
        insert(gx);
        justify(m.type, [gx.id, gx.id]);
      } else {
        const gy = goal(Y);
        insert(gx, gy);
        justify(m.type, [gx.id, gy.id]);
      }
      break;
    }
    case 'impI': {
      const b = boxWith(G.a, G.b);
      insert(b);
      justify('impI', [b.id]);
      break;
    }
    case 'notI': {
      const b = boxWith(G.a, BOT);
      insert(b);
      justify('notI', [b.id]);
      break;
    }
    case 'raa': {
      const b = boxWith(not(G), BOT);
      insert(b);
      justify('raa', [b.id]);
      break;
    }
    case 'orI': {
      const gx = goal(m.side === 'left' ? G.a : G.b);
      insert(gx);
      justify('orI', [gx.id]);
      break;
    }
    case 'contra': {
      const gb = goal(BOT);
      insert(gb);
      justify('contra', [gb.id]);
      break;
    }
    case 'andE': {
      const l = lineAt(m.lines[0]);
      insert(line(m.side === 'left' ? l.f.a : l.f.b, 'andE', [l.id]));
      break;
    }
    case 'iffE': {
      const l = lineAt(m.lines[0]);
      const f = m.side === 'left' ? imp(l.f.a, l.f.b) : imp(l.f.b, l.f.a);
      insert(line(f, 'iffE', [l.id]));
      break;
    }
    case 'impE': {
      const x = lineAt(m.lines[0]);
      const xy = lineAt(m.lines[1]);
      insert(line(xy.f.b, 'impE', [x.id, xy.id]));
      break;
    }
    case 'impEG': {
      const xy = lineAt(m.lines[0]);
      const gx = goal(xy.f.a);
      insert(gx, line(xy.f.b, 'impE', [gx.id, xy.id]));
      break;
    }
    case 'notE': {
      const a = lineAt(m.lines[0]);
      const na = lineAt(m.lines[1]);
      insert(line(BOT, 'notE', [a.id, na.id]));
      break;
    }
    case 'notEG': {
      const na = lineAt(m.lines[0]);
      const ga = goal(na.f.a);
      insert(ga, line(BOT, 'notE', [ga.id, na.id]));
      break;
    }
    case 'orE': {
      const d = lineAt(m.lines[0]);
      const b1 = boxWith(d.f.a, G);
      const b2 = boxWith(d.f.b, G);
      insert(b1, b2);
      justify('orE', [d.id, b1.id, b2.id]);
      break;
    }
    default:
      throw new Error('Unknown move ' + m.type);
  }
  autoClose(p);
  const stillOpen = new Set(openGoals(p).map((x) => x.id));
  return { proof: p, newGoals: newGoals.filter((id) => stillOpen.has(id)), created: newGoals };
}

// Formulas available to an open goal, for the oracles.
export function contextOf(p, goalId) {
  return [...new Set(visibleLines(p, goalId).map((l) => l.f))];
}

export function describeProofLines(p) {
  return toFlat(p).map((l) => `${l.num} ${'  '.repeat(l.depth)}${show(l.f)} ${l.rule ?? '?'}`).join('\n');
}

