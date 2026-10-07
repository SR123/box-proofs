// Regression tests for problems found in review.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { performance } from 'node:perf_hooks';
import { parseSequent, showSequent, show } from '../js/formula.js';
import { proveSequent } from '../js/prover.js';
import { toFlat } from '../js/proof.js';
import { checkProof } from '../js/checker.js';
import { truthTable } from '../js/semantics.js';
import { provableI } from '../js/intuitionistic.js';
import { rulesOf } from '../js/games.js';
import { rng, randomFormula } from './helpers.js';

// Lines (other than premises and the conclusion) that no later line uses.
export function unusedLines(flat) {
  const used = new Set();
  for (const l of flat) {
    for (const r of l.refs) {
      if (Array.isArray(r)) for (let k = r[0]; k <= r[1]; k++) used.add(k);
      else used.add(r);
    }
  }
  return flat.filter((l) => l.rule !== 'premise' && l.num !== flat.length && !used.has(l.num)).map((l) => l.num);
}

function proveOk(s, game, { maxLines = Infinity, maxMs = 1500 } = {}) {
  const { premises, goal } = parseSequent(s);
  const t0 = performance.now();
  const r = proveSequent(premises, goal, game);
  const ms = performance.now() - t0;
  assert.equal(r.status, 'proved', `${s} (${game}): ${r.status}`);
  const flat = toFlat(r.proof);
  const c = checkProof(flat, { premises, goal }, { rules: rulesOf(game) });
  assert.ok(c.ok, `${s}: ${JSON.stringify(c.errors)}`);
  assert.deepEqual(unusedLines(flat), [], `${s}: unused lines`);
  assert.ok(flat.length <= maxLines, `${s}: ${flat.length} lines, expected at most ${maxLines}`);
  assert.ok(ms < maxMs, `${s}: took ${ms.toFixed(0)} ms`);
  return flat;
}

// ---------------------------------------------------------------------------
// Prover: lines that contradict each other (review item L1).

test('L1: contradicting lines give a short proof with no detours', () => {
  const flat = proveOk('C → D, ¬(A ∨ B), A ⊢ E', 'or', { maxLines: 6 });
  assert.deepEqual(flat.slice(3).map((l) => l.rule), ['orI', 'notE', 'contra']);
  proveOk('P ∨ Q, ¬(A ∨ B), A ⊢ E', 'or', { maxLines: 6 });
});

test('L1: irrelevant disjunctions and implications are not split or used', () => {
  const ds = ['B ∨ C', 'D ∨ E', 'F ∨ G', 'H ∨ I', 'J ∨ K', 'L ∨ M', 'P ∨ Q', 'R ∨ S', 'T ∨ U', 'V ∨ W'];
  for (let n = 1; n <= ds.length; n++) {
    // n premises, ¬(A → A), then a box A, A → A, ⊥ and N.
    proveOk(`${ds.slice(0, n).join(', ')}, ¬(A → A) ⊢ N`, 'or', { maxLines: n + 5 });
  }
  const imps = 'B → C, D → E, F → G, H → I, J → K, L → M, ¬(A → A) ⊢ N';
  proveOk(imps, 'not', { maxLines: 11 });
  proveOk(imps, 'full', { maxLines: 11 });
});

test('L1: the minimised random example from the review is short', () => {
  proveOk('A → C ⊢ (((B ∧ A) ∨ A) → (⊥ → (¬A → ¬B))) → (¬(B ∨ ¬D) → (((A → A) → ¬D) → ¬(B → D)))', 'or', { maxLines: 14 });
  // These used to time out.
  proveOk('(((A ∨ D) → ¬D) ∧ (¬E ∨ (⊥ ∨ D))) ∧ ((C → (D ∨ D)) → E), C ∧ C ⊢ ¬¬(((B ∨ A) → (A ∧ E)) → ((D → E) ∨ B))', 'or', { maxMs: 500 });
  proveOk('((¬C → (B → A)) ∧ (C → (A → A))) → ¬((B ∨ A) → (C → C)) ⊢ ((C ∧ B) ∧ ((¬C ∨ A) ∧ ((A → A) → (B ∧ C)))) ∨ ¬((B ∨ (A ∨ B)) → ((C → C) → (B → C)))', 'or', { maxMs: 500 });
});

test('L1: random intuitionistic battery (or-game): no timeouts, no unused lines', () => {
  const r = rng(31337);
  let n = 0;
  let lines = 0;
  const times = [];
  for (let attempts = 0; attempts < 40000 && n < 400; attempts++) {
    const atoms = ['A', 'B', 'C', 'D', 'E'].slice(0, 2 + Math.floor(r() * 4));
    const premises = Array.from({ length: Math.floor(r() * 4) }, () => randomFormula(r, atoms, 1 + Math.floor(r() * 4), { iffs: false }));
    const goal = randomFormula(r, atoms, 1 + Math.floor(r() * 5), { iffs: false });
    if (!provableI(premises, goal)) continue;
    n++;
    const t0 = performance.now();
    const res = proveSequent(premises, goal, 'or');
    times.push(performance.now() - t0);
    const label = showSequent(premises, goal);
    assert.equal(res.status, 'proved', label);
    const flat = toFlat(res.proof);
    lines += flat.length;
    assert.ok(checkProof(flat, { premises, goal }, { rules: rulesOf('or') }).ok, label);
    assert.deepEqual(unusedLines(flat), [], label);
  }
  times.sort((a, b) => a - b);
  console.log('or-game battery', JSON.stringify({ n, meanLines: +(lines / n).toFixed(1), medianMs: +times[n >> 1].toFixed(2), maxMs: +times[n - 1].toFixed(1) }));
});

// ---------------------------------------------------------------------------
// Prover: the right half of ∧ intro may use the left half (review item L4).

test('L4: ∧ intro reuses its left half instead of proving it again', () => {
  const flat = proveOk('¬(D → B) ⊢ D ∧ (D ∨ B)', 'full', { maxLines: 11 });
  assert.equal(flat.filter((l) => l.rule === 'raa').length, 1, 'one contra (classical) box is enough');
  assert.ok(flat.some((l) => l.rule === 'orI' && show(l.f) === 'D ∨ B'));
});

// ---------------------------------------------------------------------------
// Prover: more than 14 atoms (review item L6).

test('L6: with more than 14 atoms an invalid sequent is invalid, not "needs classical"', () => {
  const ps = Array.from({ length: 15 }, (_, i) => `P${i + 1}`).join(' ∧ ');
  let { premises, goal } = parseSequent(`${ps} ⊢ Q`);
  assert.ok(truthTable(premises, goal).tooMany);
  assert.equal(proveSequent(premises, goal, 'and').status, 'invalid');
  assert.equal(proveSequent(premises, goal, 'full').status, 'invalid');
  ({ premises, goal } = parseSequent(`${ps} ⊢ Q ∨ ¬Q`));
  assert.equal(proveSequent(premises, goal, 'or').status, 'needsClassical');
  assert.equal(proveSequent(premises, goal, 'full').status, 'proved');
  ({ premises, goal } = parseSequent(`${ps} ⊢ Q ∨ P1`));
  assert.equal(proveSequent(premises, goal, 'or').status, 'proved');
});

// ---------------------------------------------------------------------------
// Guide.

import { newProof, openGoals, listMoves, applyMove, locate, contextOf, isComplete } from '../js/proof.js';
import {
  labelMoves, planAll, goalStatus, explainDeadEnd, moveTitle, hintText, markWithPlan, planGoal, nextMove, choiceInfo,
} from '../js/guide.js';
import { minimalGame, gameIndex } from '../js/games.js';
import { atom, not, and, or, imp, iff, BOT } from '../js/formula.js';

const strip = (html) => html.replace(/<[^>]+>/g, '');

// Apply the first rule-panel move of a type to the first open goal.
function panelMove(p, game, type, pred = () => true) {
  const g = openGoals(p)[0];
  const m = listMoves(p, g.id, game).find((x) => x.type === type && pred(x, p));
  assert.ok(m, `no ${type} move`);
  return applyMove(p, m).proof;
}

test('L2: after a roundabout move from the rule panel, the move list still offers a ✓ move', () => {
  let { premises, goal } = parseSequent('¬A, ¬(B → B) ⊢ ⊥');
  let p = panelMove(newProof(premises, goal), 'not', 'notEG', (m, q) => show(locate(q, m.lines[0]).item.f) === '¬A');
  let g = openGoals(p)[0];
  assert.equal(show(g.f), 'A');
  let labs = labelMoves(p, g.id, 'not');
  assert.ok(labs.some((l) => l.ok), 'a ✓ move for A');
  assert.equal(nextMove(p, g.id, 'not').status, 'ok');

  ({ premises, goal } = parseSequent('(D ∧ E) → A, A → (D ∧ E), D, E, F → A ⊢ D ∧ E'));
  p = panelMove(newProof(premises, goal), 'imp', 'impEG', (m, q) => show(locate(q, m.lines[0]).item.f) === 'A → (D ∧ E)');
  g = openGoals(p)[0];
  assert.equal(show(g.f), 'A');
  labs = labelMoves(p, g.id, 'imp');
  const good = labs.filter((l) => l.ok).map((l) => moveTitle(p, l.move));
  assert.deepEqual(good, ['→ elim on line 1']);
});

// Random states reached with rule-panel moves that keep every goal provable.
function* panelStates(seed, n) {
  const r = rng(seed);
  let done = 0;
  for (let attempts = 0; attempts < 20000 && done < n; attempts++) {
    const atoms = ['A', 'B', 'C', 'D'].slice(0, 2 + Math.floor(r() * 3));
    const premises = Array.from({ length: Math.floor(r() * 3) }, () => randomFormula(r, atoms, 1 + Math.floor(r() * 3)));
    const goal = randomFormula(r, atoms, 1 + Math.floor(r() * 4));
    let game = r() < 0.5 ? 'full' : minimalGame(premises, goal);
    if (gameIndex(game) < gameIndex(minimalGame(premises, goal))) game = minimalGame(premises, goal);
    const provable = (ctx, f) => (game === 'full' ? truthTable(ctx, f).valid : provableI(ctx, f));
    if (!provable(premises, goal)) continue;
    let p = newProof(premises, goal);
    const k = Math.floor(r() * 8);
    for (let i = 0; i < k && !isComplete(p); i++) {
      const goals = openGoals(p);
      const g = goals[Math.floor(r() * goals.length)];
      const ms = listMoves(p, g.id, game);
      if (!ms.length) break;
      const res = applyMove(p, ms[Math.floor(r() * ms.length)]);
      if (openGoals(res.proof).every((x) => provable(contextOf(res.proof, x.id), x.f))) p = res.proof;
    }
    if (isComplete(p)) continue;
    done++;
    yield { p, game, label: `${showSequent(premises, goal)} (${game})` };
  }
}

test('L2: in random states reached from the rule panel, every provable goal has a ✓ move', () => {
  let goals = 0;
  for (const { p, game, label } of panelStates(97, 150)) {
    for (const g of openGoals(p)) {
      goals++;
      const labs = labelMoves(p, g.id, game);
      assert.ok(labs.some((l) => l.ok), `${label}: no ✓ move for ${show(g.f)}`);
    }
  }
  assert.ok(goals >= 150);
});

test('L3: labelling the moves has one overall time budget', () => {
  const s = 'B ∨ C, D ∨ E, F ∨ G, H ∨ I, J ∨ K, L ∨ M, P ∨ Q, R ∨ S, T ∨ U, V ∨ W, ¬(A → A) ⊢ N';
  const { premises, goal } = parseSequent(s);
  const p = newProof(premises, goal);
  const t0 = performance.now();
  const labs = labelMoves(p, openGoals(p)[0].id, 'or');
  const ms = performance.now() - t0;
  assert.ok(ms < 3000, `labelMoves took ${ms.toFixed(0)} ms`);
  assert.ok(labs.find((l) => l.move.type === 'contra').ok);
  const t1 = performance.now();
  const plan = planAll(p, 'or');
  assert.equal(plan.status, 'ok');
  assert.ok(performance.now() - t1 < 1500);
  assert.equal(plan.steps.length, 3);
});

test('L4: every step Show me takes is a ✓ move of the move list (random sequents)', () => {
  const r = rng(4711);
  let n = 0;
  let steps = 0;
  for (let attempts = 0; attempts < 20000 && n < 150; attempts++) {
    const atoms = ['A', 'B', 'C', 'D'].slice(0, 2 + Math.floor(r() * 3));
    const premises = Array.from({ length: Math.floor(r() * 3) }, () => randomFormula(r, atoms, 1 + Math.floor(r() * 3)));
    const goal = randomFormula(r, atoms, 1 + Math.floor(r() * 4));
    let game = r() < 0.5 ? 'full' : minimalGame(premises, goal);
    if (gameIndex(game) < gameIndex(minimalGame(premises, goal))) game = minimalGame(premises, goal);
    if (!(game === 'full' ? truthTable(premises, goal).valid : provableI(premises, goal))) continue;
    n++;
    const label = `${showSequent(premises, goal)} (${game})`;
    const plan = planAll(newProof(premises, goal), game);
    assert.equal(plan.status, 'ok', label);
    assert.ok(checkProof(toFlat(plan.proof), { premises, goal }, { rules: rulesOf(game) }).ok, label);
    for (const step of plan.steps) {
      steps++;
      const labs = labelMoves(step.before, step.move.goalId, game);
      const same = labs.find((l) => l.move.type === step.move.type && (l.move.side || '') === (step.move.side || '')
        && (l.move.lines || []).join() === (step.move.lines || []).join());
      assert.ok(same && same.ok, `${label}: planned ${moveTitle(step.before, step.move)} is not a listed ✓ move`);
    }
  }
  assert.ok(steps > 300);
});

test('L4: Show me uses the lines already written (no second contra (classical) box)', () => {
  const { premises, goal } = parseSequent('¬(D → B) ⊢ D ∧ (D ∨ B)');
  const plan = planAll(newProof(premises, goal), 'full');
  assert.equal(plan.status, 'ok');
  const flat = toFlat(plan.proof);
  assert.equal(flat.filter((l) => l.rule === 'raa').length, 1);
  assert.ok(flat.length <= 11, `${flat.length} lines`);
  assert.deepEqual(unusedLines(flat), []);
});

test('L6: more than 14 atoms: a classically false goal is not called "only true classically"', () => {
  const ps = Array.from({ length: 15 }, (_, i) => `P${i + 1}`).join(' ∧ ');
  const { premises, goal } = parseSequent(`${ps} ⊢ Q ∨ P1`);
  const p = newProof(premises, goal);
  const labs = labelMoves(p, openGoals(p)[0].id, 'or');
  const left = labs.find((l) => l.move.type === 'orI' && l.move.side === 'left');
  assert.equal(left.ok, false);
  assert.equal(left.failing.classical, false);
  assert.doesNotMatch(strip(explainDeadEnd(left)), /classical/);
  assert.equal(labs.find((l) => l.move.type === 'orI' && l.move.side === 'right').ok, true);
  const q = applyMove(p, left.move).proof;
  const st = goalStatus(q, openGoals(q)[0].id, 'or');
  assert.equal(st.ok, false);
  assert.equal(st.classical, false);
});

test('L7: dead-end texts with no atoms or no lines read properly', () => {
  for (const s of ['⊢ (A → B) ∨ (B → A)', '⊢ ((A → B) → B) → ((B → A) → A)', '⊢ A ∨ ¬A']) {
    const { premises, goal } = parseSequent(s);
    const p = newProof(premises, goal);
    for (const lab of labelMoves(p, openGoals(p)[0].id, 'full')) {
      if (lab.ok) continue;
      const text = strip(explainDeadEnd(lab));
      assert.doesNotMatch(text, /With +all|With {2}|  /, `${s}: "${text}"`);
      if (contextOf(lab.after, lab.failing.goalId).length === 0) assert.match(text, /no lines it may use/, text);
    }
  }
});

test('L8: the move titles say what each ∧ elim and ↔ elim gives', () => {
  for (const [s, game] of [['A ∧ B ⊢ B ∧ A', 'and'], ['A ↔ B ⊢ B ↔ A', 'full'], ['A ∧ B ⊢ A ∨ B', 'or']]) {
    const { premises, goal } = parseSequent(s);
    const p = newProof(premises, goal);
    const titles = labelMoves(p, openGoals(p)[0].id, game).map((l) => moveTitle(p, l.move));
    assert.equal(new Set(titles).size, titles.length, `${s}: ${titles.join(' | ')}`);
  }
  const { premises, goal } = parseSequent('A ∧ B ⊢ B ∧ A');
  const p = newProof(premises, goal);
  const titles = labelMoves(p, openGoals(p)[0].id, 'and').map((l) => moveTitle(p, l.move));
  assert.ok(titles.includes('∧ elim on line 1: A') && titles.includes('∧ elim on line 1: B'), titles.join(' | '));
});

test('U14: a level-2 hint does not repeat the rule name', () => {
  const { premises, goal } = parseSequent('R → W, W → S ⊢ R → S');
  const p = newProof(premises, goal);
  const m = nextMove(p, openGoals(p)[0].id, 'imp').move;
  const text = strip(hintText(p, m, 2));
  assert.doesNotMatch(text, /→ intro: → intro|→ intro\. → intro/);
  assert.match(text, /^→ intro\. The goal R → S is an implication/);
});

test('U16: a safe step that the planned proof does not need is marked', () => {
  const { premises, goal } = parseSequent('A ∧ B ⊢ A ∨ B');
  let p = newProof(premises, goal);
  p = panelMove(p, 'or', 'orI', (m) => m.side === 'left');
  const g = openGoals(p)[0];
  const labs = markWithPlan(labelMoves(p, g.id, 'or'), planGoal(p, g.id, 'or'));
  const byResult = (x) => labs.find((l) => l.move.type === 'andE' && moveTitle(p, l.move).endsWith(': ' + x));
  assert.equal(byResult('A').helpful, true);
  assert.equal(byResult('B').helpful, false);
  assert.equal(choiceInfo(labs).isChoice, false);
});

// ---------------------------------------------------------------------------
// Parser and text format.

import { parseFormula, tryParseSequent } from '../js/formula.js';
import { parseProofText, proofToText } from '../js/textformat.js';

test('L9: "||-" is an error, not "or not"; "-->" means →; "|-" inside a formula is explained', () => {
  const r = tryParseSequent('A ||- B');
  assert.equal(r.ok, false);
  assert.match(r.error, /"\|\|-" is ambiguous/);
  assert.equal(parseFormula('A-->B'), imp(atom('A'), atom('B')));
  assert.equal(parseFormula('A ==> B'), imp(atom('A'), atom('B')));
  assert.equal(parseFormula('A <--> B'), iff(atom('A'), atom('B')));
  assert.equal(parseFormula('A | -B'), or(atom('A'), not(atom('B'))));
  assert.throws(() => parseFormula('A|-B'), /stands for ⊢/);
  assert.equal(tryParseSequent('A|-B').ok, true); // as a sequent it is A ⊢ B
});

test('L9: the proof reader accepts -, &&, || and v in justifications', () => {
  const cases = [
    ['1 A   - elim 1,2', 'notE'], ['1 A ∧ A   && intro 1,1', 'andI'], ['1 A ∨ B   || intro 1', 'orI'],
    ['1 C   v elim 1,2–3,4–5', 'orE'], ['1 C   ∨ elim 1,2-3,4-5', 'orE'],
  ];
  for (const [text, rule] of cases) {
    const r = parseProofText(text);
    assert.deepEqual(r.errors, [], text);
    assert.equal(r.lines[0].rule, rule, text);
  }
});

test('U26: "A v B" suggests ∨', () => {
  const r = tryParseSequent('A v B |- B v A');
  assert.equal(r.ok, false);
  assert.match(r.error, /Did you mean ∨\?/);
});

test('U10: an unfinished proof copied as text reads back, and the checker says it is not finished', () => {
  const { premises, goal } = parseSequent('R → W, W → S ⊢ R → S');
  let p = newProof(premises, goal);
  p = panelMove(p, 'imp', 'impI');
  const text = proofToText(p);
  assert.match(text, /\(goal\)/);
  const parsed = parseProofText(text);
  assert.deepEqual(parsed.errors, []);
  const c = checkProof(parsed.lines, parsed.sequent);
  assert.equal(c.ok, false);
  assert.match(c.errors[0].message, /still an open goal, so the proof is not finished/);
});

// ---------------------------------------------------------------------------
// Rule sets for imported proofs (review item L5) and export details (U31).

import { gameForRules } from '../js/games.js';
import { proofToTikz, proofToSvg } from '../js/export.js';

test('L5: the smallest rule set that contains the rules a proof uses', () => {
  assert.equal(gameForRules(new Set(['premise', 'andI', 'andE'])), 'and');
  assert.equal(gameForRules(new Set(['assumption', 'impI', 'copy'])), 'imp');
  assert.equal(gameForRules(new Set(['impI', 'notE', 'contra'])), 'not');
  assert.equal(gameForRules(new Set(['orE', 'impE'])), 'or');
  assert.equal(gameForRules(new Set(['impI', 'raa'])), 'full');
  // The checker rejects a proof that uses rules outside the given set.
  const parsed = parseProofText('1 | A            assumption\n2 | | B          assumption\n3 | | | ¬A       assumption\n4 | | | ⊥        ¬ elim 1,3\n5 | | A          contra (classical) 3–4\n6 | B → A        → intro 2–5\n7 A → (B → A)    → intro 1–6');
  const seq = parseSequent('⊢ A → (B → A)');
  assert.equal(checkProof(parsed.lines, seq).ok, true);
  const c = checkProof(parsed.lines, seq, { rules: rulesOf('imp') });
  assert.equal(c.ok, false);
  assert.ok(c.errors.some((e) => /contra \(classical\) is not available/.test(e.message)));
});

test('U31: TikZ names its ink colour bpInk and keeps case boxes apart; SVG sizes are rounded', () => {
  const { premises, goal } = parseSequent('A ∧ (B ∨ C) ⊢ (A ∧ B) ∨ (A ∧ C)');
  const proof = proveSequent(premises, goal, 'or').proof;
  const tex = proofToTikz(proof);
  assert.match(tex, /\\definecolor\{bpInk\}/);
  assert.doesNotMatch(tex, /bpink/);
  // The two case boxes of ∨ elim: the first ends at least 0.15 cm above the second.
  const rects = [...tex.matchAll(/\(([-\d.]+),([-\d.]+)\) rectangle \(([-\d.]+),([-\d.]+)\)/g)].map((m) => ({ top: +m[2], bottom: +m[4] }));
  assert.equal(rects.length, 2);
  const [first, second] = rects.sort((a, b) => b.top - a.top);
  assert.ok(first.bottom - second.top >= 0.149, `gap ${(first.bottom - second.top).toFixed(2)} cm`);
  assert.doesNotMatch(proofToSvg(proof), /\d\.\d{3,}/);
});
