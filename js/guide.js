// Guided mode: label the possible next moves as leading to a proof (✓) or
// being a dead end (✗), explain them in plain English, give hints, and
// plan a whole proof step by step for "Show me".

import { BOT, not, imp as imp2, show, showHtml } from './formula.js';
import {
  locate, listMoves, applyMove, openGoals, visibleLines, contextOf, numbering, moveResult, BACKWARD,
} from './proof.js';
import { searchTree, ProverTimeout } from './prover.js';
import { provableI, OracleTimeout } from './intuitionistic.js';
import { truthTable, showAssignment } from './semantics.js';
import { isClassical } from './games.js';

const H = (f) => `<span class="f">${showHtml(f)}</span>`;

// ---------------------------------------------------------------------------
// Is an open goal still provable from the lines available to it?
//
// Returns { ok: true } or { ok: false, classical, assignment }:
//   classical: true   the goal is true classically but needs contra (classical);
//   assignment        a truth-table row in which the lines are true and the
//                     goal is false (null when there are too many atoms).
// When the decision procedure runs out of time (only for very large
// formulas) the goal is given the benefit of the doubt: { ok: true, unknown: true }.
export function goalStatus(p, goalId, game, timeLimit = 1500) {
  const ctx = contextOf(p, goalId);
  const goal = locate(p, goalId).item.f;
  return sequentStatus(ctx, goal, game, timeLimit);
}

export function sequentStatus(ctx, goal, game, timeLimit = 1500) {
  const tt = truthTable(ctx, goal);
  if (!tt.tooMany && !tt.valid) return { ok: false, classical: false, assignment: tt.assignment };
  const deadline = Date.now() + timeLimit;
  try {
    // Too many atoms for a table: Glivenko's theorem decides classical validity.
    const classicallyValid = () => !tt.tooMany || provableI([...ctx, not(goal)], BOT, Infinity, deadline);
    if (isClassical(game)) {
      return classicallyValid() ? { ok: true } : { ok: false, classical: false, assignment: null };
    }
    if (provableI(ctx, goal, Infinity, deadline)) return { ok: true };
    return classicallyValid() ? { ok: false, classical: true } : { ok: false, classical: false, assignment: null };
  } catch (e) {
    if (e instanceof OracleTimeout) return { ok: true, unknown: true };
    throw e;
  }
}

// The open goals that cannot be proved any more: a Map from goal id to its status.
export function goalProblems(p, game) {
  const out = new Map();
  for (const g of openGoals(p)) {
    const st = goalStatus(p, g.id, game);
    if (!st.ok) out.set(g.id, st);
  }
  return out;
}

export function deadGoals(p, game) {
  return [...goalProblems(p, game).keys()];
}

// The safe forward moves never make things worse; they are not "choices".
export const SAFE = new Set(['andE', 'impE', 'notE', 'iffE']);

// Can goal gid be proved without passing through a situation it came from?
// (Uses the prover's loop-checked search, which is complete for this.)
export function provableAvoidingHistory(p, gid, game, timeLimit = 1500) {
  const g = locate(p, gid).item;
  try {
    const r = searchTree(contextOf(p, gid), g.f, game, { avoid: g.anc || [], timeLimit });
    return r.tree !== null;
  } catch (e) {
    if (e instanceof ProverTimeout) return true; // give the benefit of the doubt
    throw e;
  }
}

// All sensible moves for a goal, each applied and labelled.
//   ✓ (ok: true)  every goal the move leaves behind (its new goals, and the
//                 goal itself if still open) can still be proved;
//   ✗ (ok: false) at least one of them cannot be proved at all.
// A move whose new goals can only be proved by going back to a situation
// they came from (going round in a circle) is left out, unless every move
// that still works does that (for instance after a roundabout move from the
// rule panel); such moves are then kept and marked circular.
// The whole call has one time budget (opts.timeLimit, default 2 s): ✓/✗ is
// decided first (truth table and G4ip), and the circle check runs while time
// remains.
export function labelMoves(p, goalId, game, opts = {}) {
  const deadline = Date.now() + (opts.timeLimit ?? 2000);
  const left = () => Math.max(30, Math.min(1500, deadline - Date.now()));
  const out = [];
  for (const move of listMoves(p, goalId, game)) {
    const res = applyMove(p, move);
    const affected = [...res.newGoals];
    const g = locate(res.proof, goalId);
    const stillOpen = !!(g && g.item.k === 'line' && g.item.rule === null);
    if (stillOpen) affected.push(goalId);
    let ok = true;
    let failing = null;
    for (const id of affected) {
      const st = goalStatus(res.proof, id, game, left());
      if (!st.ok) { ok = false; failing = { goalId: id, ...st }; break; }
    }
    out.push({ move, ok, failing, after: res.proof, newGoals: res.newGoals, closes: !stillOpen && !res.newGoals.length, circular: false });
  }
  for (const lab of out) {
    if (!lab.ok || !lab.newGoals.length) continue;
    if (Date.now() > deadline) break; // out of time: benefit of the doubt
    lab.circular = lab.newGoals.some((id) => !provableAvoidingHistory(lab.after, id, game, left()));
  }
  const direct = out.filter((x) => !x.circular);
  if (direct.some((x) => x.ok)) return direct;
  return out;
}

// Number of genuine choices among the moves that lead to a proof.
export function choiceInfo(labelled) {
  const good = labelled.filter((x) => x.ok);
  const strategic = good.filter((x) => !SAFE.has(x.move.type) && x.move.type !== 'raa' && !x.circular);
  return { good: good.length, strategic: strategic.length, isChoice: strategic.length >= 2 };
}

// Moves are "the same" if they do the same thing, whichever goal they act on
// (a forward step adds the same line wherever it is used).
export function sameMoveAnyGoal(a, b) {
  return !!(a && b) && a.type === b.type && (a.side || '') === (b.side || '')
    && (a.lines || []).join(',') === (b.lines || []).join(',');
}

// Use a plan for the goal (from planGoal) to mark the moves that it uses.
//   helpful: false   a safe forward step that the planned proof does not need;
//   roundabout: true contra (classical) when a direct proof exists.
export function markWithPlan(labelled, plan) {
  if (!plan || plan.status !== 'ok' || !plan.steps.length) return labelled;
  const first = plan.steps[0].move;
  const usesRaa = plan.steps.some((s) => s.move.type === 'raa');
  for (const lab of labelled) {
    if (!lab.ok) continue;
    if (SAFE.has(lab.move.type)) lab.helpful = plan.steps.some((s) => sameMoveAnyGoal(s.move, lab.move));
    if (lab.move.type === 'raa' && first.type !== 'raa' && !usesRaa) lab.roundabout = true;
  }
  return labelled;
}

// ---------------------------------------------------------------------------
// Words.

function nums(p) {
  const nb = numbering(p);
  return (id) => nb.num.get(id);
}

function lineF(p, id) {
  return locate(p, id).item.f;
}

// The title of a move, for example "∧ elim on line 1: A".  With html: true
// the formulas are marked up (atoms in italic) and the text is escaped.
export function moveTitle(p, m, html = false) {
  const n = nums(p);
  const L = m.lines || [];
  const F = (f) => (html ? H(f) : show(f));
  const G = locate(p, m.goalId).item.f;
  switch (m.type) {
    case 'andI': return '∧ intro';
    case 'impI': return '→ intro';
    case 'notI': return '¬ intro';
    case 'iffI': return '↔ intro';
    case 'orI': return `∨ intro (${m.side}): ${F(m.side === 'left' ? G.a : G.b)}`;
    case 'contra': return 'contra';
    case 'raa': return 'contra (classical)';
    case 'andE': return `∧ elim on line ${n(L[0])}: ${F(moveResult(p, m))}`;
    case 'iffE': return `↔ elim on line ${n(L[0])}: ${F(moveResult(p, m))}`;
    case 'impE': return `→ elim on lines ${n(L[0])} and ${n(L[1])}: ${F(moveResult(p, m))}`;
    case 'impEG': return `→ elim on line ${n(L[0])}`;
    case 'notE': return `¬ elim on lines ${n(L[0])} and ${n(L[1])}`;
    case 'notEG': return `¬ elim on line ${n(L[0])}`;
    case 'orE': return `∨ elim on line ${n(L[0])}`;
    default: return m.type;
  }
}

export const RULE_OF_MOVE = {
  andI: '∧ intro', impI: '→ intro', notI: '¬ intro', iffI: '↔ intro', orI: '∨ intro',
  contra: 'contra', raa: 'contra (classical)', andE: '∧ elim', iffE: '↔ elim',
  impE: '→ elim', impEG: '→ elim', notE: '¬ elim', notEG: '¬ elim', orE: '∨ elim',
};

// What a move does, in a few words (HTML): "New goal: A", "Adds B".
export function moveEffect(p, m, lab = null) {
  const G = locate(p, m.goalId).item.f;
  const L = (m.lines || []).map((id) => lineF(p, id));
  let text;
  switch (m.type) {
    case 'andI': text = G.a === G.b ? `New goal: ${H(G.a)} (used twice)` : `New goals: ${H(G.a)} and ${H(G.b)}`; break;
    case 'impI': text = `Box assuming ${H(G.a)}, new goal ${H(G.b)}`; break;
    case 'notI': text = `Box assuming ${H(G.a)}, new goal ⊥`; break;
    case 'raa': text = `Box assuming ${H(not(G))}, new goal ⊥`; break;
    case 'iffI': text = `New goals: ${H(imp2(G.a, G.b))} and ${H(imp2(G.b, G.a))}`; break;
    case 'orI': text = `New goal: ${H(m.side === 'left' ? G.a : G.b)}`; break;
    case 'contra': text = 'New goal: ⊥'; break;
    case 'andE': case 'iffE': case 'impE': case 'notE': text = `Adds ${H(moveResult(p, m))}`; break;
    case 'impEG': text = `New goal: ${H(L[0].a)}, then adds ${H(L[0].b)}`; break;
    case 'notEG': text = `New goal: ${H(L[0].a)}, then ⊥`; break;
    case 'orE': text = `Two cases, assuming ${H(L[0].a)} and assuming ${H(L[0].b)}, each with goal ${H(G)}`; break;
    default: text = '';
  }
  if (lab && lab.closes) text += ', which closes the goal';
  return text;
}

// One or two sentences on what the move does and why.
export function explainMove(p, m) {
  const n = nums(p);
  const G = locate(p, m.goalId).item.f;
  const L = (m.lines || []).map((id) => lineF(p, id));
  const k = (i) => n(m.lines[i]);
  switch (m.type) {
    case 'impI':
      return `The goal ${H(G)} is an implication, so → intro is the natural move: open a box assuming ${H(G.a)} and aim for ${H(G.b)}.`;
    case 'andI':
      return G.a === G.b
        ? `The goal ${H(G)} is a conjunction of two equal parts. Prove ${H(G.a)} once; ∧ intro may use the same line twice.`
        : `The goal ${H(G)} is a conjunction, so a natural move is to prove ${H(G.a)} and ${H(G.b)} separately; ∧ intro then puts them together.`;
    case 'notI':
      return `The goal ${H(G)} is a negation, so ¬ intro is the natural move: open a box assuming ${H(G.a)} and aim for ⊥.`;
    case 'iffI':
      return `The goal ${H(G)} is a biconditional. Prove both implications, ${H(imp2(G.a, G.b))} and ${H(imp2(G.b, G.a))}; ↔ intro combines them.`;
    case 'orI': {
      const X = m.side === 'left' ? G.a : G.b;
      return `To prove the disjunction ${H(G)} it is enough to prove one side. This keeps the ${m.side} side: the new goal is ${H(X)}.`;
    }
    case 'contra':
      return 'From ⊥ you may conclude anything (contra). The new goal is ⊥: reach a contradiction from the lines above.';
    case 'raa':
      return `Reductio ad absurdum: assume ${H(not(G))} and aim for ⊥; contra (classical) then gives ${H(G)}. Use it when the direct moves do not work.`;
    case 'andE':
      return `Line ${k(0)} is ${H(L[0])}, so ∧ elim gives ${H(m.side === 'left' ? L[0].a : L[0].b)}.`;
    case 'iffE': {
      const f = m.side === 'left' ? imp2(L[0].a, L[0].b) : imp2(L[0].b, L[0].a);
      return `Line ${k(0)} is ${H(L[0])}, so ↔ elim gives ${H(f)}.`;
    }
    case 'impE':
      return `Lines ${k(0)} and ${k(1)} are ${H(L[0])} and ${H(L[1])}, so → elim (modus ponens) gives ${H(L[1].b)}.`;
    case 'impEG':
      return `Line ${k(0)} is ${H(L[0])}. To use it you need ${H(L[0].a)}, which becomes a new goal; then → elim gives ${H(L[0].b)}.`;
    case 'notE':
      return `Lines ${k(0)} and ${k(1)} are ${H(L[0])} and ${H(L[1])}, a contradiction, so ¬ elim gives ⊥.`;
    case 'notEG':
      return `The goal is ⊥ and line ${k(0)} is ${H(L[0])}. Prove ${H(L[0].a)}; then ¬ elim with line ${k(0)} gives ⊥.`;
    case 'orE':
      return `Line ${k(0)} is ${H(L[0])}, so argue by cases: one box assuming ${H(L[0].a)} and one assuming ${H(L[0].b)}, each aiming for ${H(G)}. ∨ elim then gives ${H(G)}.`;
    default:
      return '';
  }
}

// Why a goal cannot be proved, given the lines it may use (HTML sentence).
export function deadReason(ctx, g, st) {
  if (st.assignment) {
    const a = showAssignment(st.assignment);
    if (!ctx.length) {
      return a
        ? `${H(g)} cannot be proved from nothing: with ${a} it is false, and there are no lines it may use.`
        : `${H(g)} cannot be proved from nothing: it is false, and there are no lines it may use.`;
    }
    return a
      ? `${H(g)} does not follow from the lines it may use: with ${a} all of them are true but ${H(g)} is false.`
      : `${H(g)} does not follow from the lines it may use: they are all true, but ${H(g)} is false.`;
  }
  if (st.classical) return `${H(g)} cannot be proved with these rules. It is true classically, but it needs contra (classical).`;
  return `${H(g)} does not follow from the lines it may use (there are too many atoms to show a truth-table row).`;
}

// Why a ✗ move is a dead end.
export function explainDeadEnd(lab) {
  if (!lab.failing) return '';
  const p = lab.after;
  const id = lab.failing.goalId;
  return `Dead end: ${deadReason(contextOf(p, id), locate(p, id).item.f, lab.failing)}`;
}

// Hint text at level 1 (direction) and 2 (rule).
export function hintText(p, m, level) {
  const back = BACKWARD.has(m.type);
  const G = locate(p, m.goalId).item.f;
  const n = nums(p);
  if (level === 1) {
    if (back) {
      if (m.type === 'raa') return `Work backwards from the goal ${H(G)}. The direct moves do not work here, so think about a proof by contradiction.`;
      if (m.type === 'contra') return `Work backwards from the goal ${H(G)}: the lines above contradict each other.`;
      return `Work backwards from the goal ${H(G)}: look at its principal connective.`;
    }
    return `Work forwards: use one of the lines above the goal${m.lines ? ` (look at line ${n(m.lines[m.lines.length - 1])})` : ''}.`;
  }
  return `<b>${moveTitle(p, m, true)}</b>. ${explainMove(p, m)}`;
}

// ---------------------------------------------------------------------------
// Planning: turn a prover tree into a sequence of editor moves, in the order
// a person would build the proof: backward steps on the goal first, forward
// steps when a line is needed.

function annotate(tree) {
  const info = new Map(); // node -> { parent, depth, index, block }
  let index = 0;
  let blockCounter = 0;
  const uses = new Map(); // handle -> [node]
  const use = (h, node) => {
    if (!uses.has(h)) uses.set(h, []);
    uses.get(h).push(node);
  };
  const walk = (node, parent, block) => {
    info.set(node, { parent, depth: parent ? info.get(parent).depth + 1 : 0, index: index++, block });
    switch (node.r) {
      case 'hyp': use(node.h, node); break;
      case 'andI': case 'iffI': walk(node.l, node, block); if (!node.same) walk(node.r2, node, block); break;
      case 'orI': case 'contra': walk(node.sub, node, block); break;
      case 'impI': case 'notI': case 'raa': walk(node.body, node, ++blockCounter); break;
      case 'orE': use(node.major, node); walk(node.bodyL, node, ++blockCounter); walk(node.bodyR, node, ++blockCounter); break;
      case 'impEG': use(node.major, node); walk(node.minor, node, block); walk(node.body, node, block); break;
      case 'notEG': use(node.major, node); walk(node.minor, node, block); break;
      default: break;
    }
  };
  walk(tree, null, 0);
  const lca2 = (a, b) => {
    let x = a;
    let y = b;
    while (info.get(x).depth > info.get(y).depth) x = info.get(x).parent;
    while (info.get(y).depth > info.get(x).depth) y = info.get(y).parent;
    while (x !== y) { x = info.get(x).parent; y = info.get(y).parent; }
    return x;
  };
  const all = new Set();
  const visit = (h) => {
    if (all.has(h)) return;
    all.add(h);
    if (h.how) for (const d of h.how.refs) visit(d);
  };
  for (const h of uses.keys()) visit(h);
  const derived = [...all].filter((h) => h.kind === 'derived').sort((a, b) => b.hid - a.hid);
  const pre = new Map();
  for (const h of derived) {
    const us = uses.get(h) || [];
    if (!us.length) continue;
    const D = us.reduce(lca2);
    const first = us.reduce((a, b) => (info.get(a).index <= info.get(b).index ? a : b));
    let effective = us;
    if (info.get(first).block !== info.get(D).block) {
      if (!pre.has(D)) pre.set(D, []);
      pre.get(D).push(h);
      effective = [D];
    }
    for (const d of h.how.refs) for (const u of effective) use(d, u);
  }
  for (const list of pre.values()) list.sort((a, b) => a.hid - b.hid);
  return pre;
}

export class PlanError extends Error {}

// Apply the moves that build the proof tree for one goal.
export function realizeTree(p0, goalId, tree) {
  let cur = p0;
  const steps = [];
  const pre = annotate(tree);
  const apply = (move) => {
    const res = applyMove(cur, move);
    steps.push({ move, before: cur, after: res.proof });
    cur = res.proof;
    return res;
  };
  const isOpen = (id) => {
    const l = locate(cur, id);
    return !!(l && l.item.k === 'line' && l.item.rule === null);
  };
  const visible = (gid, f) => visibleLines(cur, gid).find((l) => l.f === f) || null;

  // Make a line with formula h.f visible from goal gid.  Returns its id, or
  // null when the goal itself got closed on the way.
  const ensure = (gid, h) => {
    const v = visible(gid, h.f);
    if (v) return v.id;
    if (h.kind !== 'derived') throw new PlanError('planner: ' + show(h.f) + ' is not available');
    const how = h.how;
    const fwd = (type, lines, side) => apply({ type, dir: 'fwd', goalId: gid, lines, ...(side ? { side } : {}) });
    switch (how.rule) {
      case 'andE': case 'iffE': {
        const c = ensure(gid, how.refs[0]);
        if (c === null) return null;
        fwd(how.rule, [c], how.side);
        break;
      }
      case 'impE': {
        const xy = ensure(gid, how.refs[1]);
        if (xy === null) return null;
        const x = ensure(gid, how.refs[0]);
        if (x === null) return null;
        fwd('impE', [x, xy]);
        break;
      }
      case 'notE': {
        const a = ensure(gid, how.refs[0]);
        if (a === null) return null;
        const na = ensure(gid, how.refs[1]);
        if (na === null) return null;
        fwd('notE', [a, na]);
        break;
      }
      default:
        throw new PlanError('planner: unknown derivation ' + how.rule);
    }
    if (!isOpen(gid)) return null;
    const made = visible(gid, h.f);
    return made ? made.id : null;
  };

  const realize = (gid, node) => {
    if (!isOpen(gid)) return;
    for (const h of pre.get(node) || []) {
      ensure(gid, h);
      if (!isOpen(gid)) return;
    }
    const back = (type, extra = {}) => apply({ type, dir: 'back', goalId: gid, ...extra }).created;
    switch (node.r) {
      case 'hyp':
        ensure(gid, node.h);
        if (isOpen(gid)) throw new PlanError('planner: goal not closed');
        return;
      case 'andI': case 'iffI': {
        const c = back(node.r);
        realize(c[0], node.l);
        if (!node.same) realize(c[1], node.r2);
        return;
      }
      case 'impI': case 'notI': case 'raa': {
        const c = back(node.r);
        realize(c[0], node.body);
        return;
      }
      case 'orI': {
        const c = back('orI', { side: node.side });
        realize(c[0], node.sub);
        return;
      }
      case 'contra': {
        const c = back('contra');
        realize(c[0], node.sub);
        return;
      }
      case 'orE': {
        const d = ensure(gid, node.major);
        if (d === null) return;
        if (visible(gid, node.hypL.f)) { realize(gid, node.bodyL); return; }
        if (visible(gid, node.hypR.f)) { realize(gid, node.bodyR); return; }
        const c = apply({ type: 'orE', dir: 'fwd', goalId: gid, lines: [d] }).created;
        realize(c[0], node.bodyL);
        realize(c[1], node.bodyR);
        return;
      }
      case 'impEG': {
        const xy = ensure(gid, node.major);
        if (xy === null) return;
        if (!visible(gid, node.hyp.f)) {
          const x = visible(gid, node.major.f.a);
          if (x) apply({ type: 'impE', dir: 'fwd', goalId: gid, lines: [x.id, xy] });
          else {
            const c = apply({ type: 'impEG', dir: 'fwd', goalId: gid, lines: [xy] }).created;
            realize(c[0], node.minor);
          }
        }
        realize(gid, node.body);
        return;
      }
      case 'notEG': {
        const na = ensure(gid, node.major);
        if (na === null) return;
        const a = visible(gid, node.major.f.a);
        if (a) apply({ type: 'notE', dir: 'fwd', goalId: gid, lines: [a.id, na] });
        else {
          const c = apply({ type: 'notEG', dir: 'fwd', goalId: gid, lines: [na] }).created;
          realize(c[0], node.minor);
        }
        return;
      }
      default:
        throw new PlanError('planner: bad node');
    }
  };
  realize(goalId, tree);
  return { steps, proof: cur };
}

// Plan the steps for one goal.  Returns { status, steps, proof, tree }.
// status: 'ok' | 'dead' (the goal cannot be proved) | 'timeout' | 'failed'.
// circular: true when the only proof goes back to a situation the goal came
// from (after a roundabout move from the rule panel).
export function planGoal(p, goalId, game, opts = {}) {
  const timeLimit = opts.timeLimit ?? 1500;
  const st = goalStatus(p, goalId, game, timeLimit);
  if (!st.ok) return { status: 'dead', steps: [], proof: p, goalId, info: st };
  const g = locate(p, goalId).item;
  try {
    const ctx = contextOf(p, goalId);
    let r = searchTree(ctx, g.f, game, { timeLimit, avoid: g.anc || [] });
    let circular = false;
    if (!r.tree && g.anc && g.anc.length) {
      r = searchTree(ctx, g.f, game, { timeLimit });
      circular = !!r.tree;
    }
    if (!r.tree) return { status: 'failed', steps: [], proof: p, goalId };
    const { steps, proof } = realizeTree(p, goalId, r.tree);
    return { status: 'ok', steps, proof, goalId, tree: r.tree, circular };
  } catch (e) {
    if (e instanceof ProverTimeout) return { status: 'timeout', steps: [], proof: p, goalId };
    throw e;
  }
}

// Does a planned step go round in a circle?  This is the test labelMoves
// uses, so that every step Show me takes is one the move list offers.
function circularStep(step, game, timeLimit) {
  const res = applyMove(step.before, step.move);
  return res.newGoals.some((id) => !provableAvoidingHistory(res.proof, id, game, timeLimit));
}

// The order in which to prefer moves when the plan has to be corrected.
function preference(lab) {
  const t = lab.move.type;
  if (t === 'raa') return 5;
  if (t === 'contra') return 4;
  if (SAFE.has(t)) return 3;
  return lab.move.dir === 'back' ? 1 : 2;
}

// The first step of a plan for goal gid, checked against the move list: if
// the planned step goes round in a circle, the best non-circular ✓ move is
// used instead.  Returns { status, step, circular } (step: { move, before, after }).
export function planFirstStep(p, gid, game, opts = {}) {
  const r = planGoal(p, gid, game, opts);
  if (r.status !== 'ok' || !r.steps.length) return { status: r.status === 'ok' ? 'done' : r.status, info: r.info, plan: r };
  const step = r.steps[0];
  if (r.circular || !circularStep(step, game, opts.timeLimit ?? 1500)) return { status: 'ok', step, plan: r, circular: !!r.circular };
  const alt = labelMoves(p, gid, game, { timeLimit: opts.timeLimit ?? 1500 })
    .filter((l) => l.ok && !l.circular)
    .sort((a, b) => preference(a) - preference(b))[0];
  if (!alt) return { status: 'ok', step, plan: r, circular: true };
  return { status: 'ok', step: { move: alt.move, before: p, after: alt.after }, plan: r, corrected: true };
}

// Plan the whole remaining proof, in the order a person would build it.
// The first open goal is planned from the current state; its steps are
// taken until one of them finishes a goal, and then the next goal is planned
// afresh, so that it can use the lines written in the meantime (for example
// the left half of an ∧ intro).  A step that would go round in a circle is
// replaced by a move from the move list.  opts.timeLimit is for the whole plan.
export function planAll(p, game, opts = {}) {
  const deadline = Date.now() + (opts.timeLimit ?? 3000);
  let cur = p;
  const steps = [];
  for (let guard = 0; guard < 500; guard++) {
    const goals = openGoals(cur);
    if (!goals.length) return { status: 'ok', steps, proof: cur };
    const left = () => Math.max(30, Math.min(1500, deadline - Date.now()));
    if (deadline - Date.now() <= 0) return { status: 'timeout', steps, proof: cur };
    const r = planGoal(cur, goals[0].id, game, { timeLimit: left() });
    if (r.status !== 'ok') return { ...r, steps, proof: cur };
    let before = goals.length;
    for (const step of r.steps) {
      if (!r.circular && circularStep(step, game, left())) {
        const alt = labelMoves(step.before, step.move.goalId, game, { timeLimit: left() })
          .filter((l) => l.ok && !l.circular)
          .sort((a, b) => preference(a) - preference(b))[0];
        if (alt) {
          steps.push({ move: alt.move, before: step.before, after: alt.after });
          cur = alt.after;
          break; // plan afresh from here
        }
      }
      steps.push(step);
      cur = step.after;
      const now = openGoals(cur).length;
      if (now < before) break; // a goal is finished: plan the next one afresh
      before = now;
    }
  }
  return { status: 'failed', steps, proof: cur };
}

// The next planned move for a goal (for hints).
export function nextMove(p, goalId, game, opts = {}) {
  const r = planFirstStep(p, goalId, game, opts);
  if (r.status !== 'ok') return { status: r.status, info: r.info };
  return { status: 'ok', move: r.step.move, circular: r.circular };
}
