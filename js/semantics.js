// Truth tables: classical validity and counterexamples.

import { atomsOf } from './formula.js';

export const MAX_ATOMS = 14;

// Evaluate f under an assignment given as a Map or plain object name -> boolean.
export function evaluate(f, v) {
  switch (f.t) {
    case 'atom': return !!(v instanceof Map ? v.get(f.name) : v[f.name]);
    case 'bot': return false;
    case 'not': return !evaluate(f.a, v);
    case 'and': return evaluate(f.a, v) && evaluate(f.b, v);
    case 'or': return evaluate(f.a, v) || evaluate(f.b, v);
    case 'imp': return !evaluate(f.a, v) || evaluate(f.b, v);
    case 'iff': return evaluate(f.a, v) === evaluate(f.b, v);
    default: throw new Error('unknown formula ' + f.t);
  }
}

// Compile a formula to a function of a bit mask (bit i = value of atom i).
function compile(f, index) {
  switch (f.t) {
    case 'atom': {
      const bit = 1 << index.get(f.name);
      return (m) => (m & bit) !== 0;
    }
    case 'bot': return () => false;
    case 'not': { const a = compile(f.a, index); return (m) => !a(m); }
    case 'and': { const a = compile(f.a, index), b = compile(f.b, index); return (m) => a(m) && b(m); }
    case 'or': { const a = compile(f.a, index), b = compile(f.b, index); return (m) => a(m) || b(m); }
    case 'imp': { const a = compile(f.a, index), b = compile(f.b, index); return (m) => !a(m) || b(m); }
    case 'iff': { const a = compile(f.a, index), b = compile(f.b, index); return (m) => a(m) === b(m); }
    default: throw new Error('unknown formula ' + f.t);
  }
}

// Check premises ⊢ goal with a truth table.
// Returns { valid: true } or { valid: false, assignment: {A: 1, B: 0, ...}, atoms }
// or { tooMany: true, atoms } when there are more than MAX_ATOMS atoms.
export function truthTable(premises, goal, maxAtoms = MAX_ATOMS) {
  const atoms = atomsOf([...premises, goal]);
  if (atoms.length > maxAtoms) return { tooMany: true, atoms };
  const index = new Map(atoms.map((a, i) => [a, i]));
  const ps = premises.map((p) => compile(p, index));
  const g = compile(goal, index);
  const rows = 1 << atoms.length;
  // Enumerate so that the first atom is the most significant "digit" and
  // rows with 1s come first, matching the usual hand-written tables.
  for (let r = 0; r < rows; r++) {
    let m = 0;
    for (let i = 0; i < atoms.length; i++) {
      const bit = (r >> (atoms.length - 1 - i)) & 1;
      if (bit === 0) m |= 1 << i; // r = 0 means all atoms true
    }
    if (ps.every((p) => p(m)) && !g(m)) {
      const assignment = {};
      atoms.forEach((a, i) => { assignment[a] = (m >> i) & 1; });
      return { valid: false, assignment, atoms };
    }
  }
  return { valid: true, atoms };
}

const memo = new Map();

// Cached classical validity, used for labelling moves in the full rule set.
// Returns true, false, or null when there are too many atoms.
export function classicallyValid(premises, goal) {
  const key = premises.map((p) => p.id).sort((x, y) => x - y).join(',') + '|' + goal.id;
  if (memo.has(key)) return memo.get(key);
  const r = truthTable(premises, goal);
  const v = r.tooMany ? null : r.valid;
  if (memo.size > 50000) memo.clear();
  memo.set(key, v);
  return v;
}

export function showAssignment(assignment) {
  return Object.entries(assignment).map(([a, v]) => `${a} = ${v}`).join(', ');
}
