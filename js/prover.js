// The automatic prover.
//
// 1. A truth table decides classical validity (up to 14 atoms) and gives a
//    counterexample when the sequent is not valid.
// 2. A goal-directed natural deduction search finds a proof that uses only
//    the course rules.  It works like an intercalation calculus: intro rules
//    backwards on the goal, elim rules forwards from the available lines,
//    with loop checking on (available formulas, goal).  An intuitionistic
//    decision procedure (G4ip) is used as an oracle to prune dead branches,
//    so the search rarely backtracks.
// 3. If the sequent is classically valid but has no intuitionistic proof,
//    the goal is broken up by the invertible rules (→ intro, ∧ intro,
//    ¬ intro) and each remaining goal X is proved by contra (classical):
//    assume ¬X and derive ⊥ intuitionistically.  By Glivenko's theorem this
//    always succeeds.
//
// Proof trees.  Each node proves a formula f:
//   { r: 'hyp', h }                         use an available line
//   { r: 'andI'|'iffI', l, r2, same }       same: both halves are one line
//   { r: 'impI'|'notI'|'raa', hyp, body }   a box with assumption hyp
//   { r: 'orI', side, sub }
//   { r: 'contra', sub }                    sub proves ⊥
//   { r: 'orE', major, hypL, bodyL, hypR, bodyR }
//   { r: 'impEG', major, minor, hyp, body } → elim with X proved first;
//                                           hyp is the new line Y
//   { r: 'notEG', major, minor }            minor proves A; gives ⊥
// Handles h = { hid, f, kind: 'base'|'assume'|'impEG'|'lemma'|'derived', how }
// stand for lines; derived ones (from ∧ elim, → elim, ¬ elim, ↔ elim) record
// how they were obtained and are written out only when used.  A 'lemma' is
// the left half of an ∧ intro (or ↔ intro), which the right half may use:
// andI/iffI nodes carry it as lh.
//
// Inconsistent lines.  When the available lines already contradict each
// other, every goal follows, so the oracle prunes nothing.  The search then
// goes for ⊥ first (and contra), proves ⊥ from a minimal set of
// contradicting lines, and drops case splits and → elim steps whose new line
// is never used.  This keeps the proofs short and the search fast.

import { BOT, not, imp, show, subformulas } from './formula.js';
import { provableI, OracleTimeout } from './intuitionistic.js';
import { truthTable } from './semantics.js';
import { rulesOf, minimalGame, gameIndex, isClassical, gameById } from './games.js';

export class ProverTimeout extends Error {}

// Step limit for each oracle call that minimises a set of contradicting lines.
const RESTRICT_STEPS = 2000;

// Does the proof tree use handle target (directly, or through the lines
// derived from it)?
export function usesHandle(tree, target) {
  const seen = new Set();
  const visitH = (h) => {
    if (h === target) return true;
    if (seen.has(h)) return false;
    seen.add(h);
    return !!(h.how && h.how.refs.some(visitH));
  };
  const walk = (n) => {
    switch (n.r) {
      case 'hyp': return visitH(n.h);
      case 'andI': case 'iffI': return walk(n.l) || (!n.same && walk(n.r2));
      case 'orI': case 'contra': return walk(n.sub);
      case 'impI': case 'notI': case 'raa': return walk(n.body);
      case 'orE': return visitH(n.major) || walk(n.bodyL) || walk(n.bodyR);
      case 'impEG': return visitH(n.major) || walk(n.minor) || walk(n.body);
      case 'notEG': return visitH(n.major) || walk(n.minor);
      default: return false;
    }
  };
  return walk(tree);
}

class Ctx {
  constructor(map) {
    this.map = map;
    this._key = null;
  }
  has(f) { return this.map.has(f); }
  get(f) { return this.map.get(f); }
  add(h) {
    const m = new Map(this.map);
    m.set(h.f, h);
    return new Ctx(m);
  }
  formulas() { return [...this.map.keys()]; }
  handles() { return [...this.map.values()].sort((a, b) => a.hid - b.hid); }
  key() {
    if (this._key === null) this._key = [...this.map.keys()].map((f) => f.id).sort((a, b) => a - b).join(',');
    return this._key;
  }
}

function makeSearch(game, opts) {
  const R = rulesOf(game);
  let hid = 0;
  let nodes = 0;
  const deadline = opts.deadline ?? Infinity;
  const maxNodes = opts.maxNodes ?? Infinity;
  const useOracle = opts.useOracle !== false;

  const handle = (f, kind, how = null) => ({ hid: ++hid, f, kind, how });

  // A local budget (nodes and time) for one sub-search (see withLocalLimit).
  let localLimit = Infinity;
  let localDeadline = Infinity;
  class LocalLimit extends Error {}

  const oracle = (ctx, g) => {
    if (!useOracle) return true;
    try {
      return provableI(ctx.formulas(), g, Infinity, Math.min(deadline, localDeadline));
    } catch (e) {
      if (e instanceof OracleTimeout) throw Date.now() > deadline ? new ProverTimeout() : new LocalLimit();
      throw e;
    }
  };

  const tick = () => {
    nodes++;
    if (nodes > maxNodes) throw new ProverTimeout();
    if (nodes > localLimit) throw new LocalLimit();
    if ((nodes & 63) === 0) {
      const now = Date.now();
      if (now > deadline) throw new ProverTimeout();
      if (now > localDeadline) throw new LocalLimit();
    }
  };

  // A share of the remaining time, for a sub-search that has a fallback.
  const timeShare = () => (deadline === Infinity ? 1500 : Math.max(150, (deadline - Date.now()) * 0.3));

  // Run fn with at most n more search nodes and ms more milliseconds.
  // Returns { value } or { limited: true } when the budget ran out.
  function withLocalLimit(fn, n, ms = timeShare()) {
    const saved = [localLimit, localDeadline];
    localLimit = Math.min(saved[0], nodes + n);
    localDeadline = Math.min(saved[1], Date.now() + ms);
    const mine = [localLimit, localDeadline];
    try {
      return { value: fn() };
    } catch (e) {
      if (e instanceof LocalLimit && (mine[0] < saved[0] || mine[1] < saved[1])
        && (nodes > mine[0] || Date.now() > mine[1]) && nodes <= saved[0] && Date.now() <= saved[1]) {
        return { limited: true };
      }
      throw e;
    } finally {
      [localLimit, localDeadline] = saved;
    }
  }

  function saturate(ctx) {
    let c = ctx;
    let changed = true;
    while (changed) {
      changed = false;
      for (const h of c.handles()) {
        const f = h.f;
        const add = (g, how) => {
          if (!c.has(g)) {
            c = c.add(handle(g, 'derived', how));
            changed = true;
          }
        };
        if (f.t === 'and' && R.has('andE')) {
          add(f.a, { rule: 'andE', refs: [h], side: 'left' });
          add(f.b, { rule: 'andE', refs: [h], side: 'right' });
        } else if (f.t === 'iff' && R.has('iffE')) {
          add(imp(f.a, f.b), { rule: 'iffE', refs: [h], side: 'left' });
          add(imp(f.b, f.a), { rule: 'iffE', refs: [h], side: 'right' });
        } else if (f.t === 'imp' && R.has('impE') && c.has(f.a)) {
          add(f.b, { rule: 'impE', refs: [c.get(f.a), h] });
        } else if (f.t === 'not' && R.has('notE') && c.has(f.a)) {
          add(BOT, { rule: 'notE', refs: [c.get(f.a), h] });
        }
      }
    }
    return c;
  }

  function closeBy(ctx, goal) {
    const h = ctx.get(goal);
    if (h) return { r: 'hyp', f: goal, h };
    if (goal !== BOT && R.has('contra')) {
      const hb = ctx.get(BOT);
      if (hb) return { r: 'contra', f: goal, sub: { r: 'hyp', f: BOT, h: hb } };
    }
    return null;
  }

  // Implications ordered so that those ending in the goal come first.
  function orderImps(hs, goal) {
    const score = (h) => {
      const y = h.f.b;
      if (y === goal) return 0;
      if (subformulas([y]).includes(goal)) return 1;
      return 2;
    };
    return hs.slice().sort((a, b) => score(a) - score(b) || a.hid - b.hid);
  }

  function search(ctx0, G, path) {
    tick();
    let ctx = ctx0;
    let c = closeBy(ctx, G);
    if (c) return c;
    ctx = saturate(ctx);
    c = closeBy(ctx, G);
    if (c) return c;
    const key = ctx.key() + '|' + G.id;
    if (path.has(key)) return null;
    if (!oracle(ctx, G)) return null;
    path.add(key);
    try {
      return candidates(ctx, G, path);
    } finally {
      path.delete(key);
    }
  }

  // A minimal set of lines that still contradict each other (for a goal ⊥).
  // Older lines are dropped first, so the newest assumptions are kept.
  const restrictMemo = new Map();
  function restrictForBottom(ctx) {
    const hs = ctx.handles();
    if (hs.length <= 1) return ctx;
    const key = ctx.key();
    let keepIds = restrictMemo.get(key);
    if (!keepIds) {
      let keep = hs.map((h) => h.f);
      for (const h of hs) {
        const trial = keep.filter((f) => f !== h.f);
        let still;
        try {
          // A capped check: if it is too costly, keep the line (the set
          // still contradicts itself, it is just not minimal).
          still = provableI(trial, BOT, RESTRICT_STEPS, Math.min(deadline, localDeadline));
        } catch (e) {
          if (!(e instanceof OracleTimeout)) throw e;
          if (Date.now() > deadline) throw new ProverTimeout();
          if (Date.now() > localDeadline) throw new LocalLimit();
          still = false;
        }
        if (still) keep = trial;
      }
      keepIds = new Set(keep.map((f) => f.id));
      restrictMemo.set(key, keepIds);
    }
    if (keepIds.size === hs.length) return ctx;
    return new Ctx(new Map(hs.filter((h) => keepIds.has(h.f.id)).map((h) => [h.f, h])));
  }

  function candidates(ctx, G, path) {
    if (useOracle && G === BOT) {
      // Prove ⊥ from the lines that matter; fall back to all lines.
      const S = restrictForBottom(ctx);
      if (S !== ctx) {
        // The restricted situation is on the path too, so that its subgoals
        // do not go back to ⊥ by contra.
        const key = S.key() + '|' + BOT.id;
        const fresh = !path.has(key);
        if (fresh) path.add(key);
        let t;
        try {
          t = candidatesIn(S, G, path, false, true);
        } finally {
          if (fresh) path.delete(key);
        }
        if (t) return t;
      }
      return candidatesIn(ctx, G, path, false);
    }
    // The lines contradict each other: aim for ⊥, then contra.  (An
    // implication or a negation is opened with its intro rule first, as the
    // strategy says; the contradiction is then found inside the box.)
    if (useOracle && R.has('contra') && G.t !== 'imp' && G.t !== 'not' && oracle(ctx, BOT)) {
      const sub = search(ctx, BOT, path);
      if (sub) return { r: 'contra', f: G, sub };
      return candidatesIn(ctx, G, path, false);
    }
    return candidatesIn(ctx, G, path, true);
  }

  // ctx without one line (and so without what was derived from it alone).
  function dropHandle(ctx, h) {
    const m = new Map(ctx.map);
    m.delete(h.f);
    return new Ctx(m);
  }

  // minimal: ctx is a minimal set of contradicting lines and G is ⊥.  Then
  // the lines without the major premise of ¬ elim or → elim are consistent,
  // so the minor premise is searched there, where the oracle can prune.
  function candidatesIn(ctx, G, path, tryContra, minimal = false) {
    // Invertible backward steps.
    if (G.t === 'imp' && R.has('impI')) {
      const hx = handle(G.a, 'assume');
      const body = search(ctx.add(hx), G.b, path);
      if (body) return { r: 'impI', f: G, hyp: hx, body };
    }
    if (G.t === 'and' && R.has('andI')) {
      const l = search(ctx, G.a, path);
      if (l) {
        if (G.a === G.b) return { r: 'andI', f: G, l, r2: l, same: true };
        // The right half may use the left half's conclusion.
        const lh = ctx.has(G.a) ? null : handle(G.a, 'lemma');
        const r2 = search(lh ? ctx.add(lh) : ctx, G.b, path);
        if (r2) return { r: 'andI', f: G, l, r2, lh };
      }
    }
    if (G.t === 'not' && R.has('notI')) {
      const hx = handle(G.a, 'assume');
      const body = search(ctx.add(hx), BOT, path);
      if (body) return { r: 'notI', f: G, hyp: hx, body };
    }
    if (G.t === 'iff' && R.has('iffI')) {
      const X = imp(G.a, G.b);
      const Y = imp(G.b, G.a);
      const l = search(ctx, X, path);
      if (l) {
        if (X === Y) return { r: 'iffI', f: G, l, r2: l, same: true };
        const lh = ctx.has(X) ? null : handle(X, 'lemma');
        const r2 = search(lh ? ctx.add(lh) : ctx, Y, path);
        if (r2) return { r: 'iffI', f: G, l, r2, lh };
      }
    }
    // ∨ intro when one side already follows.
    if (G.t === 'or' && R.has('orI')) {
      // A side that is already available comes first.
      const sides = ctx.has(G.b) && !ctx.has(G.a) ? ['right', 'left'] : ['left', 'right'];
      for (const side of sides) {
        const X = side === 'left' ? G.a : G.b;
        if (side === 'right' && G.a === G.b) break;
        if (!oracle(ctx, X)) continue;
        const sub = search(ctx, X, path);
        if (sub) return { r: 'orI', f: G, side, sub };
      }
    }
    const hs = ctx.handles();
    // ∨ elim on an available disjunction.
    if (R.has('orE')) {
      for (const h of hs) {
        if (h.f.t !== 'or') continue;
        const { a, b } = h.f;
        if (ctx.has(a) || ctx.has(b)) continue;
        const hl = handle(a, 'assume');
        const hr = handle(b, 'assume');
        const cl = ctx.add(hl);
        const cr = ctx.add(hr);
        if (!oracle(cl, G) || !oracle(cr, G)) continue;
        const bodyL = search(cl, G, path);
        if (!bodyL) continue;
        // A case that never uses its assumption proves G outright.
        if (!usesHandle(bodyL, hl)) return bodyL;
        const bodyR = search(cr, G, path);
        if (!bodyR) continue;
        if (!usesHandle(bodyR, hr)) return bodyR;
        return { r: 'orE', f: G, major: h, hypL: hl, bodyL, hypR: hr, bodyR };
      }
    }
    // → elim where the antecedent becomes a new goal.
    if (R.has('impE')) {
      for (const h of orderImps(hs.filter((x) => x.f.t === 'imp'), G)) {
        const { a: X, b: Y } = h.f;
        if (ctx.has(X) || ctx.has(Y) || X === G) continue;
        const mctx = minimal ? dropHandle(ctx, h) : ctx;
        if (!oracle(mctx, X)) continue;
        const hy = handle(Y, 'impEG');
        const cy = ctx.add(hy);
        if (!oracle(cy, G)) continue;
        // The rest first: if it does not need Y, the → elim step is not needed.
        const body = search(cy, G, path);
        if (!body) continue;
        if (!usesHandle(body, hy)) return body;
        const minor = search(mctx, X, path);
        if (!minor) continue;
        return { r: 'impEG', f: G, major: h, minor, hyp: hy, body };
      }
    }
    // ¬ elim on a goal ⊥ where A becomes a new goal.
    if (G === BOT && R.has('notE')) {
      for (const h of hs) {
        if (h.f.t !== 'not') continue;
        const A = h.f.a;
        if (ctx.has(A) || A === BOT) continue;
        const mctx = minimal ? dropHandle(ctx, h) : ctx;
        if (!oracle(mctx, A)) continue;
        const minor = search(mctx, A, path);
        if (minor) return { r: 'notEG', f: BOT, major: h, minor };
      }
    }
    // contra: aim for ⊥ instead.
    if (tryContra && G !== BOT && R.has('contra') && oracle(ctx, BOT)) {
      const sub = search(ctx, BOT, path);
      if (sub) return { r: 'contra', f: G, sub };
    }
    return null;
  }

  // A classical refutation tableau, written out with the course rules.
  // Returns a proof of ⊥ from ctx, which must be classically inconsistent.
  // Signed formulas: T(X) is an available line X; F(X) means that a proof of
  // X would give ⊥ (it comes from a line ¬X, possibly through ∨ intro).
  // α rules come first, then β rules (branching); each signed formula is
  // expanded at most once on a branch, so the tableau always terminates.
  function tableau(ctx0, done) {
    tick();
    const ctx = saturate(ctx0);
    const hb = ctx.get(BOT);
    if (hb) return { r: 'hyp', f: BOT, h: hb };
    const F = [];
    const addF = (f, close) => {
      if (f === BOT) return;
      if (f.t === 'or') {
        addF(f.a, (t) => close({ r: 'orI', f, side: 'left', sub: t }));
        if (f.b !== f.a) addF(f.b, (t) => close({ r: 'orI', f, side: 'right', sub: t }));
        return;
      }
      F.push({ f, close });
    };
    const hs = ctx.handles();
    for (const h of hs) if (h.f.t === 'not') addF(h.f.a, (t) => ({ r: 'notEG', f: BOT, major: h, minor: t }));
    // Closure: X is available and a proof of X gives ⊥.
    for (const x of F) {
      const h = ctx.get(x.f);
      if (h) return x.close({ r: 'hyp', f: x.f, h });
    }
    const mark = (key) => new Set(done).add(key);
    // Prove X by contra (classical), continuing the tableau with ¬X.
    const byRaa = (c, X, d) => {
      if (c.has(X)) return { r: 'hyp', f: X, h: c.get(X) };
      if (X === BOT) return tableau(c, d);
      const hn = handle(not(X), 'assume');
      return { r: 'raa', f: X, hyp: hn, body: tableau(c.add(hn), d) };
    };
    // α rules on F: F(¬A) gives T(A); F(A → B) gives T(A) and F(B).
    for (const x of F) {
      const key = 'F' + x.f.id;
      if (done.has(key)) continue;
      if (x.f.t === 'not') {
        const hx = handle(x.f.a, 'assume');
        return x.close({ r: 'notI', f: x.f, hyp: hx, body: tableau(ctx.add(hx), mark(key)) });
      }
      if (x.f.t === 'imp') {
        const ha = handle(x.f.a, 'assume');
        return x.close({ r: 'impI', f: x.f, hyp: ha, body: byRaa(ctx.add(ha), x.f.b, mark(key)) });
      }
    }
    // β rules on T: A ∨ B (∨ elim) and A → B (→ elim, with A by contra (classical)).
    for (const h of hs) {
      const f = h.f;
      const key = 'T' + f.id;
      if (done.has(key)) continue;
      if (f.t === 'or' && !ctx.has(f.a) && !ctx.has(f.b)) {
        const d = mark(key);
        const hl = handle(f.a, 'assume');
        const hr = handle(f.b, 'assume');
        return { r: 'orE', f: BOT, major: h, hypL: hl, bodyL: tableau(ctx.add(hl), d), hypR: hr, bodyR: tableau(ctx.add(hr), d) };
      }
      if (f.t === 'imp' && f.a !== BOT && !ctx.has(f.a) && !ctx.has(f.b)) {
        const d = mark(key);
        const hy = handle(f.b, 'impEG');
        return { r: 'impEG', f: BOT, major: h, minor: byRaa(ctx, f.a, d), hyp: hy, body: tableau(ctx.add(hy), d) };
      }
    }
    // β rules on F: A ∧ B and A ↔ B.
    for (const x of F) {
      const key = 'F' + x.f.id;
      if (done.has(key)) continue;
      const d = mark(key);
      if (x.f.t === 'and') {
        const l = byRaa(ctx, x.f.a, d);
        if (x.f.a === x.f.b) return x.close({ r: 'andI', f: x.f, l, r2: l, same: true });
        return x.close({ r: 'andI', f: x.f, l, r2: byRaa(ctx, x.f.b, d) });
      }
      if (x.f.t === 'iff') {
        const half = (X, Y) => {
          const hx = handle(X, 'assume');
          return { r: 'impI', f: imp(X, Y), hyp: hx, body: byRaa(ctx.add(hx), Y, d) };
        };
        const l = half(x.f.a, x.f.b);
        if (x.f.a === x.f.b) return x.close({ r: 'iffI', f: x.f, l, r2: l, same: true });
        return x.close({ r: 'iffI', f: x.f, l, r2: half(x.f.b, x.f.a) });
      }
    }
    throw new Error('tableau: the lines are consistent, so there is no proof of ⊥');
  }

  // Nodes the intuitionistic search may use under contra (classical) before
  // the tableau takes over.
  const CLASSICAL_BUDGET = 3000;

  // Prove ⊥ from a classically inconsistent ctx: the intuitionistic search
  // usually finds the short textbook proof; the tableau is the safety net.
  function bottom(ctx, path) {
    const r = withLocalLimit(() => search(ctx, BOT, path), CLASSICAL_BUDGET);
    if (!r.limited) return r.value;
    return tableau(ctx, new Set());
  }

  // Classical proof: intuitionistic if possible, otherwise invertible steps
  // and then contra (classical) on the remaining goal.
  function classical(ctx, G, path) {
    tick();
    const sat = saturate(ctx);
    const direct = closeBy(sat, G);
    if (direct) return search(ctx, G, path);
    let intuitionistic = null;
    if (useOracle) {
      const o = withLocalLimit(() => oracle(sat, G), Infinity);
      intuitionistic = o.limited ? 'slow' : o.value;
    }
    if (intuitionistic === true) {
      const r = withLocalLimit(() => search(ctx, G, path), CLASSICAL_BUDGET * 3);
      if (!r.limited && r.value) return r.value;
      if (r.limited) {
        // The search is lost in an inconsistent context: argue classically.
        if (G === BOT) return tableau(ctx, new Set());
        const hn = handle(not(G), 'assume');
        return { r: 'raa', f: G, hyp: hn, body: tableau(ctx.add(hn), new Set()) };
      }
      // No direct proof avoids the situations on the path: argue classically
      // below.
    }
    if (intuitionistic === null) {
      const t = search(ctx, G, path);
      if (t) return t;
    }
    const key = sat.key() + '|' + G.id;
    if (path.has(key)) return null;
    path.add(key);
    try {
      return decompose(ctx, G, path);
    } finally {
      path.delete(key);
    }
  }

  function decompose(ctx, G, path) {
    switch (G.t) {
      case 'imp': {
        const hx = handle(G.a, 'assume');
        const body = classical(ctx.add(hx), G.b, path);
        return body && { r: 'impI', f: G, hyp: hx, body };
      }
      case 'and': {
        const l = classical(ctx, G.a, path);
        if (!l) return null;
        if (G.a === G.b) return { r: 'andI', f: G, l, r2: l, same: true };
        const lh = ctx.has(G.a) ? null : handle(G.a, 'lemma');
        const r2 = classical(lh ? ctx.add(lh) : ctx, G.b, path);
        return r2 && { r: 'andI', f: G, l, r2, lh };
      }
      case 'iff': {
        const X = imp(G.a, G.b);
        const Y = imp(G.b, G.a);
        const l = classical(ctx, X, path);
        if (!l) return null;
        if (X === Y) return { r: 'iffI', f: G, l, r2: l, same: true };
        const lh = ctx.has(X) ? null : handle(X, 'lemma');
        const r2 = classical(lh ? ctx.add(lh) : ctx, Y, path);
        return r2 && { r: 'iffI', f: G, l, r2, lh };
      }
      case 'not': {
        const hx = handle(G.a, 'assume');
        const body = bottom(ctx.add(hx), path);
        return body && { r: 'notI', f: G, hyp: hx, body };
      }
      default: {
        if (G === BOT) return null;
        const hn = handle(not(G), 'assume');
        const body = bottom(ctx.add(hn), path);
        return body && { r: 'raa', f: G, hyp: hn, body };
      }
    }
  }

  function baseCtx(ctxFormulas) {
    let ctx = new Ctx(new Map());
    const base = [];
    for (const f of ctxFormulas) {
      const h = handle(f, 'base');
      base.push(h);
      if (!ctx.has(f)) ctx = ctx.add(h);
    }
    return { ctx, base };
  }

  return {
    handle,
    // avoid: situations { ctx, goal } that the proof must not pass through.
    run(ctxFormulas, goal, avoid = []) {
      const { ctx, base } = baseCtx(ctxFormulas);
      const path = new Set(avoid.map((s) => this.key(s.ctx, s.goal)));
      const tree = R.has('raa') ? classical(ctx, goal, path) : search(ctx, goal, path);
      return { tree, base, nodes };
    },
    // The loop-checking key of a situation: saturated formulas and goal.
    key(ctxFormulas, goal) {
      return saturate(baseCtx(ctxFormulas).ctx).key() + '|' + goal.id;
    },
    get nodes() { return nodes; },
  };
}

// Find a proof tree of ctx ⊢ goal with the rules of a game.
// opts.avoid lists situations { ctx, goal } the proof may not pass through
// (the guide uses this so that it never suggests going round in a circle).
// Returns { tree, base, nodes } (tree null if none) or throws ProverTimeout.
export function searchTree(ctxFormulas, goal, game, opts = {}) {
  const s = makeSearch(game, {
    deadline: opts.timeLimit != null ? Date.now() + opts.timeLimit : opts.deadline,
    maxNodes: opts.maxNodes,
    useOracle: opts.useOracle,
  });
  return s.run(ctxFormulas, goal, opts.avoid || []);
}

// ---------------------------------------------------------------------------
// From a proof tree to the editor's proof model.

function commonPrefix(paths) {
  let p = paths[0].slice();
  for (const q of paths) {
    let k = 0;
    while (k < p.length && k < q.length && p[k] === q[k]) k++;
    p = p.slice(0, k);
  }
  return p;
}

// Collect the handles a tree uses, and in which block (box) each use sits.
function analyseUses(tree) {
  let blockCounter = 0;
  const uses = new Map();
  const addUse = (h, path) => {
    if (!uses.has(h)) uses.set(h, []);
    uses.get(h).push(path);
  };
  const walk = (node, path) => {
    switch (node.r) {
      case 'hyp': addUse(node.h, path); break;
      case 'andI': case 'iffI':
        walk(node.l, path);
        if (!node.same) walk(node.r2, path);
        break;
      case 'orI': case 'contra': walk(node.sub, path); break;
      case 'impI': case 'notI': case 'raa': {
        const b = ++blockCounter;
        node._blk = b;
        walk(node.body, [...path, b]);
        break;
      }
      case 'orE': {
        addUse(node.major, path);
        const b1 = ++blockCounter;
        const b2 = ++blockCounter;
        node._blkL = b1;
        node._blkR = b2;
        walk(node.bodyL, [...path, b1]);
        walk(node.bodyR, [...path, b2]);
        break;
      }
      case 'impEG': addUse(node.major, path); walk(node.minor, path); walk(node.body, path); break;
      case 'notEG': addUse(node.major, path); walk(node.minor, path); break;
      default: throw new Error('bad node ' + node.r);
    }
  };
  walk(tree, [0]);
  const all = new Set();
  const visit = (h) => {
    if (all.has(h)) return;
    all.add(h);
    if (h.how) for (const d of h.how.refs) visit(d);
  };
  for (const h of uses.keys()) visit(h);
  const derived = [...all].filter((h) => h.kind === 'derived').sort((a, b) => b.hid - a.hid);
  const lca = new Map();
  for (const h of derived) {
    const p = commonPrefix(uses.get(h));
    lca.set(h, p);
    for (const d of h.how.refs) addUse(d, p);
  }
  return lca;
}

// Turn a proof tree into a complete proof in the editor model.
// baseHandles[i] is the handle of premises[i].
export function treeToProof(premises, goal, tree, baseHandles) {
  const lca = analyseUses(tree);
  const p = { premises: premises.slice(), goal, items: [], nextId: 1 };
  const mk = (f, rule, refs = []) => ({ k: 'line', id: p.nextId++, f, rule, refs });
  const blocks = new Map([[0, { items: p.items, insertAt: null }]]);
  const lineOf = new Map();
  premises.forEach((f, i) => {
    const l = mk(f, 'premise');
    p.items.push(l);
    lineOf.set(baseHandles[i], l.id);
  });
  // Several base handles may share a formula; map all of them.
  const byFormula = new Map();
  baseHandles.forEach((h, i) => { if (!byFormula.has(h.f)) byFormula.set(h.f, lineOf.get(baseHandles[i])); });
  for (const h of baseHandles) if (!lineOf.has(h)) lineOf.set(h, byFormula.get(h.f));

  const append = (b, item) => blocks.get(b).items.push(item);
  const put = (b, item) => {
    const B = blocks.get(b);
    if (B.insertAt === null) B.items.push(item);
    else B.items.splice(B.insertAt++, 0, item);
  };
  const need = (h) => {
    if (lineOf.has(h)) return lineOf.get(h);
    if (h.kind !== 'derived') throw new Error('internal: line for ' + show(h.f) + ' is missing');
    // Write the implication before its antecedent (A, then B → C, then B, then C).
    const order = h.how.rule === 'impE' ? [h.how.refs[1], h.how.refs[0]] : h.how.refs.slice().sort((x, y) => x.hid - y.hid);
    for (const d of order) need(d);
    const refs = h.how.refs.map((d) => lineOf.get(d));
    const path = lca.get(h);
    const l = mk(h.f, h.how.rule, refs);
    put(path[path.length - 1], l);
    lineOf.set(h, l.id);
    return l.id;
  };
  const ensureLast = (items, id, f) => {
    const last = items[items.length - 1];
    if (last && last.k === 'line' && last.id === id) return;
    items.push(mk(f, 'copy', [id]));
  };
  const openBox = (b, blk, hyp) => {
    const box = { k: 'box', id: p.nextId++, items: [] };
    append(b, box);
    blocks.set(blk, { items: box.items, insertAt: null });
    const a = mk(hyp.f, 'assumption');
    box.items.push(a);
    lineOf.set(hyp, a.id);
    return box;
  };

  const emit = (node, b) => {
    switch (node.r) {
      case 'hyp': return need(node.h);
      case 'andI': case 'iffI': {
        const i = emit(node.l, b);
        if (node.lh) lineOf.set(node.lh, i);
        const j = node.same ? i : emit(node.r2, b);
        const l = mk(node.f, node.r, [i, j]);
        append(b, l);
        return l.id;
      }
      case 'orI': case 'contra': {
        const i = emit(node.sub, b);
        const l = mk(node.f, node.r, [i]);
        append(b, l);
        return l.id;
      }
      case 'impI': case 'notI': case 'raa': {
        const B = blocks.get(b);
        const box = openBox(b, node._blk, node.hyp);
        B.insertAt = B.items.length - 1;
        const r = emit(node.body, node._blk);
        ensureLast(box.items, r, node.body.f);
        B.insertAt = null;
        const l = mk(node.f, node.r, [box.id]);
        append(b, l);
        return l.id;
      }
      case 'orE': {
        const k = need(node.major);
        const B = blocks.get(b);
        const box1 = openBox(b, node._blkL, node.hypL);
        B.insertAt = B.items.length - 1;
        ensureLast(box1.items, emit(node.bodyL, node._blkL), node.f);
        const box2 = openBox(b, node._blkR, node.hypR);
        ensureLast(box2.items, emit(node.bodyR, node._blkR), node.f);
        B.insertAt = null;
        const l = mk(node.f, 'orE', [k, box1.id, box2.id]);
        append(b, l);
        return l.id;
      }
      case 'impEG': {
        const i = emit(node.minor, b);
        const j = need(node.major);
        const l = mk(node.hyp.f, 'impE', [i, j]);
        append(b, l);
        lineOf.set(node.hyp, l.id);
        return emit(node.body, b);
      }
      case 'notEG': {
        const i = emit(node.minor, b);
        const j = need(node.major);
        const l = mk(BOT, 'notE', [i, j]);
        append(b, l);
        return l.id;
      }
      default:
        throw new Error('bad node ' + node.r);
    }
  };
  const r = emit(tree, 0);
  ensureLast(p.items, r, goal);
  return p;
}

export function treeSize(t) {
  if (!t) return 0;
  switch (t.r) {
    case 'hyp': return 0;
    case 'andI': case 'iffI': return 1 + treeSize(t.l) + (t.same ? 0 : treeSize(t.r2));
    case 'orI': case 'contra': return 1 + treeSize(t.sub);
    case 'impI': case 'notI': case 'raa': return 2 + treeSize(t.body);
    case 'orE': return 3 + treeSize(t.bodyL) + treeSize(t.bodyR);
    case 'impEG': return 1 + treeSize(t.minor) + treeSize(t.body);
    case 'notEG': return 1 + treeSize(t.minor);
    default: return 0;
  }
}

// ---------------------------------------------------------------------------
// The top-level entry point.
//
// Returns one of
//   { status: 'proved', proof, tree, ms, nodes }
//   { status: 'invalid', assignment, atoms }      a counterexample
//   { status: 'needsClassical' }                  valid, but not with these rules
//   { status: 'needsRules', game }                the sequent uses connectives the game lacks
//   { status: 'timeout', ms }
export function proveSequent(premises, goal, game = 'full', opts = {}) {
  const t0 = Date.now();
  const timeLimit = opts.timeLimit ?? 1500;
  const deadline = t0 + timeLimit;
  const need = minimalGame(premises, goal);
  if (gameIndex(game) < gameIndex(need)) return { status: 'needsRules', game: need };
  const tt = truthTable(premises, goal);
  if (!tt.tooMany && !tt.valid) return { status: 'invalid', assignment: tt.assignment, atoms: tt.atoms };
  try {
    if (!isClassical(game) || tt.tooMany) {
      const intu = provableI(premises, goal, Infinity, deadline);
      if (!intu) {
        // Too many atoms for a table: decide classical validity by Glivenko.
        const classicallyValid = !tt.tooMany || provableI([...premises, not(goal)], BOT, Infinity, deadline);
        if (!classicallyValid) return { status: 'invalid', assignment: null, atoms: tt.atoms };
        if (!isClassical(game)) return { status: 'needsClassical' };
      }
    }
    const { tree, base, nodes } = searchTree(premises, goal, game, { deadline, useOracle: opts.useOracle });
    if (!tree) return { status: 'failed', ms: Date.now() - t0 };
    const proof = treeToProof(premises, goal, tree, base);
    return { status: 'proved', proof, tree, ms: Date.now() - t0, nodes };
  } catch (e) {
    if (e instanceof ProverTimeout || e instanceof OracleTimeout) return { status: 'timeout', ms: Date.now() - t0 };
    throw e;
  }
}

// Decide whether ctx ⊢ goal can be proved with the rules of a game.
export function decide(ctx, goal, game, deadline = Infinity) {
  if (isClassical(game)) {
    const tt = truthTable(ctx, goal);
    if (!tt.tooMany) return tt.valid;
    return provableI([...ctx, not(goal)], BOT, Infinity, deadline);
  }
  return provableI(ctx, goal, Infinity, deadline);
}

export { gameById };
