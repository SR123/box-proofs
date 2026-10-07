// A decision procedure for intuitionistic propositional logic: Dyckhoff's
// contraction-free sequent calculus G4ip.  It always terminates, so it can be
// used as an oracle ("is this goal still provable from these lines?") by the
// natural deduction prover and the guided mode.
//
// ¬A is treated as A → ⊥ and A ↔ B as (A → B) ∧ (B → A).

import { BOT, imp } from './formula.js';

const memo = new Map();
let steps = 0;
let maxSteps = Infinity;
let deadline = Infinity;

export class OracleTimeout extends Error {}

// Is ctx ⊢ goal intuitionistically valid?  ctx is an array of formulas.
// Throws OracleTimeout when the step limit or the deadline (a Date.now()
// value) is reached.
export function provableI(ctx, goal, stepLimit = Infinity, deadlineAt = Infinity) {
  const saved = [steps, maxSteps, deadline];
  steps = 0;
  maxSteps = stepLimit;
  deadline = deadlineAt;
  try {
    return prove(ctx, goal);
  } finally {
    [steps, maxSteps, deadline] = saved;
  }
}

export function clearOracleCache() { memo.clear(); }

// Bring the context into normal form by applying all invertible left rules
// that do not branch.  Returns null when ⊥ is derivable at once.
function normalise(list) {
  const atoms = new Set();
  const pending = new Map(); // atom -> formulas B with (atom → B) waiting for the atom
  const disj = [];
  const impimp = []; // formulas (C → D) → B
  const seen = new Set();
  const work = list.slice();
  while (work.length) {
    const f = work.pop();
    if (seen.has(f)) continue;
    seen.add(f);
    switch (f.t) {
      case 'bot': return null;
      case 'atom': {
        atoms.add(f);
        const waiting = pending.get(f);
        if (waiting) { pending.delete(f); for (const b of waiting) work.push(b); }
        break;
      }
      case 'and': work.push(f.a, f.b); break;
      case 'iff': work.push(imp(f.a, f.b), imp(f.b, f.a)); break;
      case 'or': disj.push(f); break;
      case 'not': work.push(imp(f.a, BOT)); break;
      case 'imp': {
        const c = f.a;
        const b = f.b;
        switch (c.t) {
          case 'atom':
            if (atoms.has(c)) work.push(b);
            else {
              if (!pending.has(c)) pending.set(c, []);
              pending.get(c).push(b);
            }
            break;
          case 'bot': break; // ⊥ → B carries no information
          case 'and': work.push(imp(c.a, imp(c.b, b))); break;
          case 'or': work.push(imp(c.a, b), imp(c.b, b)); break;
          case 'iff': work.push(imp(imp(c.a, c.b), imp(imp(c.b, c.a), b))); break;
          case 'not': impimp.push(imp(imp(c.a, BOT), b)); break;
          case 'imp': impimp.push(f); break;
          default: throw new Error('bad formula');
        }
        break;
      }
      default: throw new Error('bad formula');
    }
  }
  const pend = [];
  for (const [p, bs] of pending) for (const b of bs) pend.push(imp(p, b));
  const irr = [...atoms, ...pend, ...disj, ...impimp];
  // Deduplicate (impimp may contain a formula twice via different routes).
  const uniq = [...new Set(irr)];
  const key = uniq.map((f) => f.id).sort((x, y) => x - y).join(',');
  return { atoms, disj: [...new Set(disj)], impimp: [...new Set(impimp)], irr: uniq, key };
}

function without(arr, f) {
  return arr.filter((x) => x !== f);
}

function prove(ctx, goal) {
  steps++;
  if (steps > maxSteps) throw new OracleTimeout('oracle step limit');
  if ((steps & 255) === 0 && Date.now() > deadline) throw new OracleTimeout('oracle time limit');
  const st = normalise(ctx);
  if (st === null) return true;
  const key = st.key + '|' + goal.id;
  const hit = memo.get(key);
  if (hit !== undefined) return hit;
  const r = proveNormal(st, goal);
  if (memo.size > 400000) memo.clear();
  memo.set(key, r);
  return r;
}

function proveNormal(st, goal) {
  // Invertible right rules.
  switch (goal.t) {
    case 'and': return prove(st.irr, goal.a) && prove(st.irr, goal.b);
    case 'imp': return prove([...st.irr, goal.a], goal.b);
    case 'not': return prove([...st.irr, goal.a], BOT);
    case 'iff':
      return prove([...st.irr, goal.a], goal.b) && prove([...st.irr, goal.b], goal.a);
    case 'atom':
      if (st.atoms.has(goal)) return true;
      break;
    default: break;
  }
  // Invertible left rule for ∨.
  if (st.disj.length) {
    const d = st.disj[0];
    const rest = without(st.irr, d);
    return prove([...rest, d.a], goal) && prove([...rest, d.b], goal);
  }
  // Non-invertible choices.
  if (goal.t === 'or') {
    if (prove(st.irr, goal.a) || prove(st.irr, goal.b)) return true;
  }
  for (const f of st.impimp) {
    const c = f.a.a;
    const d = f.a.b;
    const b = f.b;
    const rest = without(st.irr, f);
    if (prove([...rest, imp(d, b)], imp(c, d)) && prove([...rest, b], goal)) return true;
  }
  return false;
}
