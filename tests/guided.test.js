import { test } from 'node:test';
import assert from 'node:assert/strict';
import { performance } from 'node:perf_hooks';
import { parseSequent, show } from '../js/formula.js';
import { newProof, openGoals, isComplete, toFlat, locate, contextOf, applyMove } from '../js/proof.js';
import { checkProof } from '../js/checker.js';
import { labelMoves, planAll, planGoal, choiceInfo, explainMove, moveTitle, hintText } from '../js/guide.js';
import { searchTree } from '../js/prover.js';
import { truthTable } from '../js/semantics.js';
import { rulesOf, isClassical } from '../js/games.js';
import { EXERCISES } from '../js/exercises.js';
import { rng, pick } from './helpers.js';

const VALID = EXERCISES.filter((e) => !e.invalid);

// Independent check that a goal cannot be proved: for the full rules a
// truth-table counterexample; otherwise an exhaustive loop-checked search
// that does not use the G4ip oracle.
function reallyUnprovable(p, goalId, game) {
  const ctx = contextOf(p, goalId);
  const goal = locate(p, goalId).item.f;
  if (isClassical(game)) return !truthTable(ctx, goal).valid;
  const r = searchTree(ctx, goal, game, { useOracle: false, timeLimit: 5000 });
  return r.tree === null;
}

test('random walks over ✓ moves always reach a complete, checked proof', () => {
  let walks = 0;
  let totalSteps = 0;
  let deadChecked = 0;
  const t0 = performance.now();
  VALID.forEach((ex, idx) => {
    const { premises, goal } = parseSequent(ex.sequent);
    for (let run = 0; run < 4; run++) {
      const r = rng(1000 * (idx + 1) + run);
      let p = newProof(premises, goal);
      let steps = 0;
      while (!isComplete(p)) {
        assert.ok(steps < 250, `${ex.id}: the walk is too long`);
        const g = pick(r, openGoals(p));
        const labelled = labelMoves(p, g.id, ex.game);
        const good = labelled.filter((l) => l.ok);
        assert.ok(good.length > 0, `${ex.id}: no ✓ move for ${show(g.f)} (step ${steps})`);
        // Now and then, check a ✗ move independently.
        const badOnes = labelled.filter((l) => !l.ok);
        if (badOnes.length && r() < 0.35) {
          const b = pick(r, badOnes);
          assert.ok(reallyUnprovable(b.after, b.failing.goalId, ex.game), `${ex.id}: ✗ move ${b.move.type} is not a dead end`);
          deadChecked++;
        }
        p = pick(r, good).after;
        steps++;
      }
      const c = checkProof(toFlat(p), { premises, goal }, { rules: rulesOf(ex.game) });
      assert.ok(c.ok, `${ex.id} run ${run}: ${JSON.stringify(c.errors)}`);
      walks++;
      totalSteps += steps;
    }
  });
  console.log('guided random walks', JSON.stringify({ walks, totalSteps, deadEndsVerified: deadChecked, ms: Math.round(performance.now() - t0) }));
});

test('every ✗ move at the start of every exercise really is a dead end', () => {
  let checked = 0;
  for (const ex of VALID) {
    const { premises, goal } = parseSequent(ex.sequent);
    const p = newProof(premises, goal);
    for (const g of openGoals(p)) {
      for (const lab of labelMoves(p, g.id, ex.game)) {
        if (lab.ok) continue;
        assert.ok(reallyUnprovable(lab.after, lab.failing.goalId, ex.game), `${ex.id}: ${lab.move.type}`);
        checked++;
      }
    }
  }
  assert.ok(checked > 10);
});

test('∨ intro on ⊢ A ∨ ¬A is a dead end, contra (classical) is not', () => {
  const { premises, goal } = parseSequent('⊢ A ∨ ¬A');
  const p = newProof(premises, goal);
  const labs = labelMoves(p, openGoals(p)[0].id, 'full');
  const byType = (t, side) => labs.find((l) => l.move.type === t && (!side || l.move.side === side));
  assert.equal(byType('orI', 'left').ok, false);
  assert.equal(byType('orI', 'right').ok, false);
  assert.equal(byType('raa').ok, true);
  assert.match(explainMove(p, byType('raa').move), /assume/);
});

test('explanations name the principal connective', () => {
  const { premises, goal } = parseSequent('⊢ A → (B → A)');
  const p = newProof(premises, goal);
  const labs = labelMoves(p, openGoals(p)[0].id, 'imp');
  assert.equal(labs.length, 1);
  assert.equal(labs[0].ok, true);
  const text = explainMove(p, labs[0].move).replace(/<[^>]+>/g, '');
  assert.equal(text, 'The goal A → (B → A) is an implication, so → intro is the natural move: open a box assuming A and aim for B → A.');
  assert.match(hintText(p, labs[0].move, 1), /Work backwards/);
  assert.match(hintText(p, labs[0].move, 2), /→ intro/);
});

test('Show me plans a complete proof for every exercise, mixing backward and forward steps', () => {
  let mixed = 0;
  for (const ex of VALID) {
    const { premises, goal } = parseSequent(ex.sequent);
    const plan = planAll(newProof(premises, goal), ex.game);
    assert.equal(plan.status, 'ok', ex.id);
    assert.ok(isComplete(plan.proof), ex.id);
    assert.ok(checkProof(toFlat(plan.proof), { premises, goal }, { rules: rulesOf(ex.game) }).ok, ex.id);
    // Each planned step is one of the moves the guide would list, labelled ✓.
    for (const step of plan.steps) {
      const labs = labelMoves(step.before, step.move.goalId, ex.game);
      const same = labs.find((l) => l.move.type === step.move.type && (l.move.side || '') === (step.move.side || '')
        && (l.move.lines || []).join() === (step.move.lines || []).join());
      assert.ok(same, `${ex.id}: planned ${moveTitle(step.before, step.move)} is not listed`);
      assert.ok(same.ok, `${ex.id}: planned ${moveTitle(step.before, step.move)} is not ✓`);
    }
    const dirs = new Set(plan.steps.map((s) => s.move.dir));
    if (dirs.size === 2) mixed++;
  }
  assert.ok(mixed > 10);
});

test('choice points: A ∧ B ⊢ B ∧ A has no strategic choice; A ∨ B ⊢ B ∨ A needs ∨ elim', () => {
  let { premises, goal } = parseSequent('A ∧ B ⊢ B ∧ A');
  let p = newProof(premises, goal);
  let info = choiceInfo(labelMoves(p, openGoals(p)[0].id, 'and'));
  assert.equal(info.isChoice, false);
  ({ premises, goal } = parseSequent('A ∨ B ⊢ B ∨ A'));
  p = newProof(premises, goal);
  const labs = labelMoves(p, openGoals(p)[0].id, 'or');
  assert.deepEqual(labs.filter((l) => l.ok).map((l) => l.move.type), ['orE']);
});

test('hints for a dead goal say so', () => {
  const { premises, goal } = parseSequent('⊢ A ∨ ¬A');
  const p0 = newProof(premises, goal);
  const g = openGoals(p0)[0].id;
  const move = labelMoves(p0, g, 'full').find((l) => l.move.type === 'orI' && l.move.side === 'left').move;
  const p1 = applyMove(p0, move).proof;
  const r = planGoal(p1, openGoals(p1)[0].id, 'full');
  assert.equal(r.status, 'dead');
});

test('no circular moves are listed (→ elim backwards on its own antecedent)', () => {
  // B needs a backward step (∧ intro), so it cannot be reached by forward steps alone.
  const { premises, goal } = parseSequent('A → B, B → A, (C ∧ D) → B, C, D ⊢ A');
  let p = newProof(premises, goal);
  // Walk: use → elim on B → A, leaving goal B.
  const g = openGoals(p)[0].id;
  const labs = labelMoves(p, g, 'imp');
  const m = labs.find((l) => l.move.type === 'impEG' && show(locate(p, l.move.lines[0]).item.f) === 'B → A');
  assert.ok(m && m.ok);
  p = m.after;
  const g2 = openGoals(p)[0];
  assert.equal(show(g2.f), 'B');
  // From goal B, → elim on A → B would bring back goal A in the same situation.
  const labs2 = labelMoves(p, g2.id, 'imp');
  assert.ok(!labs2.some((l) => l.move.type === 'impEG' && show(locate(p, l.move.lines[0]).item.f) === 'A → B'));
  assert.ok(labs2.some((l) => l.ok));
});

test('notEG: with ¬(A ∨ ¬A) available, goal ⊥ can ask for A ∨ ¬A', () => {
  const { premises, goal } = parseSequent('¬(A ∨ ¬A) ⊢ ⊥');
  const p = newProof(premises, goal);
  const labs = labelMoves(p, openGoals(p)[0].id, 'or');
  const m = labs.find((l) => l.move.type === 'notEG');
  assert.ok(m && m.ok);
});
