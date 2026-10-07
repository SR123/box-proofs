import { test } from 'node:test';
import assert from 'node:assert/strict';
import { performance } from 'node:perf_hooks';
import { parseSequent, showSequent, show } from '../js/formula.js';
import { proveSequent, searchTree, treeToProof } from '../js/prover.js';
import { toFlat } from '../js/proof.js';
import { checkProof } from '../js/checker.js';
import { truthTable, evaluate } from '../js/semantics.js';
import { provableI } from '../js/intuitionistic.js';
import { rulesOf } from '../js/games.js';
import { EXERCISES } from '../js/exercises.js';
import { rng, randomFormula } from './helpers.js';

function assertFalsifies(premises, goal, assignment) {
  const v = new Map(Object.entries(assignment).map(([k, x]) => [k, !!x]));
  for (const p of premises) assert.equal(evaluate(p, v), true, `premise ${show(p)} should be true`);
  assert.equal(evaluate(goal, v), false, `goal ${show(goal)} should be false`);
}

function stats(times) {
  const sorted = times.slice().sort((a, b) => a - b);
  const sum = times.reduce((a, b) => a + b, 0);
  return {
    n: times.length,
    meanMs: +(sum / times.length).toFixed(2),
    medianMs: +sorted[Math.floor(sorted.length / 2)].toFixed(2),
    maxMs: +sorted[sorted.length - 1].toFixed(2),
  };
}

test('every shipped exercise gets a checked proof (or a correct counterexample)', () => {
  const times = [];
  for (const ex of EXERCISES) {
    const { premises, goal } = parseSequent(ex.sequent);
    const t0 = performance.now();
    const r = proveSequent(premises, goal, ex.game);
    times.push(performance.now() - t0);
    if (ex.invalid) {
      assert.equal(r.status, 'invalid', ex.id);
      assertFalsifies(premises, goal, r.assignment);
      continue;
    }
    assert.equal(r.status, 'proved', `${ex.id}: ${ex.sequent}`);
    const c = checkProof(toFlat(r.proof), { premises, goal }, { rules: rulesOf(ex.game) });
    assert.ok(c.ok, `${ex.id}: ${JSON.stringify(c.errors)}`);
  }
  console.log('exercise prover timings', JSON.stringify(stats(times)));
});

test('the "Can you prove it?" exercise shows A = 1, B = 1, C = 0', () => {
  const { premises, goal } = parseSequent('⊢ A → (B → C)');
  const r = proveSequent(premises, goal, 'imp');
  assert.equal(r.status, 'invalid');
  assert.deepEqual(r.assignment, { A: 1, B: 1, C: 0 });
});

test('classical exercises need contra (classical); the restricted games say so', () => {
  for (const s of ['¬¬A ⊢ A', '⊢ A ∨ ¬A', '⊢ ((A → B) → A) → A', '¬(A ∧ B) ⊢ ¬A ∨ ¬B', 'A → B ⊢ ¬A ∨ B']) {
    const { premises, goal } = parseSequent(s);
    assert.equal(proveSequent(premises, goal, 'or').status, 'needsClassical', s);
    const r = proveSequent(premises, goal, 'full');
    assert.equal(r.status, 'proved', s);
    const flat = toFlat(r.proof);
    assert.ok(flat.some((l) => l.rule === 'raa'), `${s} uses contra (classical)`);
    assert.ok(checkProof(flat, { premises, goal }).ok, s);
  }
});

test('a game without the needed connective rules is reported', () => {
  const { premises, goal } = parseSequent('A ⊢ A ∨ B');
  assert.equal(proveSequent(premises, goal, 'imp').status, 'needsRules');
});

test('proofs only use the rules of the chosen game', () => {
  const { premises, goal } = parseSequent('A ∧ (B ∧ C) ⊢ (A ∧ B) ∧ C');
  const r = proveSequent(premises, goal, 'and');
  const used = new Set(toFlat(r.proof).map((l) => l.rule));
  for (const rule of used) assert.ok(['premise', 'andI', 'andE', 'copy'].includes(rule), rule);
});

test('more valid sequents, including ↔ and larger ones', () => {
  const list = [
    'A ↔ B ⊢ B ↔ A',
    '⊢ (A ↔ B) → ((B ↔ C) → (A ↔ C))',
    '⊢ ¬(A ∨ B) ↔ (¬A ∧ ¬B)',
    '⊢ (A → B) ∨ (B → A)',
    '⊢ (A → B) → ((A ∨ C) → (B ∨ C))',
    'A ∨ B, ¬A ⊢ B',
    '⊢ (A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C))',
    '⊢ (A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C))',
    '(P → Q) ∧ (R → S), P ∨ R ⊢ Q ∨ S',
    '⊢ ¬¬(A ∨ ¬A)',
    '⊢ ((A → B) → A) → ((B → A) → A)',
    'A → (B ∨ C), B → D, C → D ⊢ A → D',
    '⊢ (A → (B → C)) ↔ ((A ∧ B) → C)',
    '⊢ (¬A → A) → A',
    '⊢ A ∨ (A → B)',
    '⊢ (A → B) → ((¬A → B) → B)',
    'p → q, q → r, r → s, s → t ⊢ p → t',
    '⊢ (A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5) → (A5 ∧ A4 ∧ A3 ∧ A2 ∧ A1)',
  ];
  const times = [];
  for (const s of list) {
    const { premises, goal } = parseSequent(s);
    const t0 = performance.now();
    const r = proveSequent(premises, goal, 'full', { timeLimit: 3000 });
    times.push(performance.now() - t0);
    assert.equal(r.status, 'proved', s);
    const c = checkProof(toFlat(r.proof), { premises, goal });
    assert.ok(c.ok, `${s}: ${JSON.stringify(c.errors)}`);
  }
  console.log('hand-picked sequent timings', JSON.stringify(stats(times)));
});

// Random sequents over 2–4 atoms: goals of depth up to 4, premises of depth
// up to 3.  Sampled so that about half are valid.
function randomBattery(seed, wantValid, wantInvalid, opts = {}) {
  const r = rng(seed);
  const out = [];
  let valid = 0;
  let invalid = 0;
  for (let attempts = 0; attempts < 50000 && (valid < wantValid || invalid < wantInvalid); attempts++) {
    const nAtoms = 2 + Math.floor(r() * 3);
    const atoms = ['A', 'B', 'C', 'D'].slice(0, nAtoms);
    const nPrem = Math.floor(r() * 3);
    const premises = Array.from({ length: nPrem }, () => randomFormula(r, atoms, 1 + Math.floor(r() * 3), opts));
    const goal = randomFormula(r, atoms, 1 + Math.floor(r() * 4), opts);
    const tt = truthTable(premises, goal);
    if (tt.valid && valid >= wantValid) continue;
    if (!tt.valid && invalid >= wantInvalid) continue;
    if (tt.valid) valid++; else invalid++;
    out.push({ premises, goal, tt });
  }
  return out;
}

test('random battery (320 sequents): a checked proof exactly when the truth table says valid', () => {
  const battery = randomBattery(2026, 170, 150);
  assert.ok(battery.length >= 300);
  const times = [];
  let proved = 0;
  let refuted = 0;
  let classical = 0;
  for (const { premises, goal, tt } of battery) {
    const t0 = performance.now();
    const r = proveSequent(premises, goal, 'full', { timeLimit: 4000 });
    times.push(performance.now() - t0);
    const label = showSequent(premises, goal);
    if (tt.valid) {
      assert.equal(r.status, 'proved', label);
      const flat = toFlat(r.proof);
      const c = checkProof(flat, { premises, goal });
      assert.ok(c.ok, `${label}: ${JSON.stringify(c.errors)}`);
      if (flat.some((l) => l.rule === 'raa')) classical++;
      proved++;
    } else {
      assert.equal(r.status, 'invalid', label);
      assertFalsifies(premises, goal, r.assignment);
      refuted++;
    }
  }
  console.log('random battery', JSON.stringify({ proved, refuted, usedContraClassical: classical, ...stats(times) }));
});

test('intuitionistic battery: G4ip agrees with a plain loop-checked search, and the proofs check', () => {
  // No ↔ here, so that the or-game rules apply.
  const battery = randomBattery(77, 120, 60, { iffs: false });
  let agree = 0;
  let inconclusive = 0;
  let intuitionistic = 0;
  const times = [];
  for (const { premises, goal } of battery) {
    const label = showSequent(premises, goal);
    const oracle = provableI(premises, goal);
    let plain = null;
    try {
      const t0 = performance.now();
      plain = searchTree(premises, goal, 'or', { useOracle: false, timeLimit: 3000 }).tree;
      times.push(performance.now() - t0);
    } catch (e) {
      inconclusive++;
      continue;
    }
    assert.equal(plain !== null, oracle, `G4ip and plain search disagree on ${label}`);
    agree++;
    if (oracle) {
      intuitionistic++;
      const r = proveSequent(premises, goal, 'or');
      assert.equal(r.status, 'proved', label);
      assert.ok(checkProof(toFlat(r.proof), { premises, goal }, { rules: rulesOf('or') }).ok, label);
      // The plain search's proof also checks.
      const res = searchTree(premises, goal, 'or', { useOracle: false, timeLimit: 3000 });
      const p = treeToProof(premises, goal, res.tree, res.base);
      assert.ok(checkProof(toFlat(p), { premises, goal }, { rules: rulesOf('or') }).ok, label);
    }
  }
  assert.ok(inconclusive <= battery.length * 0.05, `too many timeouts: ${inconclusive}`);
  console.log('intuitionistic battery', JSON.stringify({ agree, inconclusive, intuitionistic, plainSearch: stats(times) }));
});

test('too many atoms for a truth table: the prover still decides', () => {
  const atoms = Array.from({ length: 16 }, (_, i) => `P${i}`);
  const chain = atoms.slice(0, -1).map((a, i) => `${a} → ${atoms[i + 1]}`).join(', ');
  const { premises, goal } = parseSequent(`${chain} ⊢ P0 → P15`);
  const r = proveSequent(premises, goal, 'full', { timeLimit: 3000 });
  assert.equal(r.status, 'proved');
  assert.ok(checkProof(toFlat(r.proof), { premises, goal }).ok);
});

test('stress: 60 larger valid sequents (goals of depth 5 over 4 atoms)', () => {
  const r = rng(4242);
  const times = [];
  let n = 0;
  for (let attempts = 0; attempts < 100000 && n < 60; attempts++) {
    const atoms = ['A', 'B', 'C', 'D'];
    const premises = Array.from({ length: Math.floor(r() * 3) }, () => randomFormula(r, atoms, 3));
    const goal = randomFormula(r, atoms, 5);
    if (goal.size < 9 || !truthTable(premises, goal).valid) continue;
    n++;
    const t0 = performance.now();
    const res = proveSequent(premises, goal, 'full', { timeLimit: 4000 });
    times.push(performance.now() - t0);
    const label = showSequent(premises, goal);
    assert.equal(res.status, 'proved', label);
    assert.ok(checkProof(toFlat(res.proof), { premises, goal }).ok, label);
  }
  console.log('stress battery', JSON.stringify(stats(times)));
});
