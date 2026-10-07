import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  atom, not, and, or, imp, iff, BOT, parseFormula, parseSequent, tryParseSequent,
  show, showAscii, showLatex, showSequent, ParseError, atomsOf,
} from '../js/formula.js';
import { rng, randomFormula } from './helpers.js';

const A = atom('A');
const B = atom('B');
const C = atom('C');

test('hash-consing: equal formulas are the same object', () => {
  assert.equal(and(A, B), and(atom('A'), atom('B')));
  assert.equal(parseFormula('A ∧ B'), parseFormula('(A) & (B)'));
  assert.notEqual(and(A, B), and(B, A));
});

test('printing follows the slides: brackets inside binary formulas, none outside', () => {
  assert.equal(show(imp(A, imp(B, A))), 'A → (B → A)');
  assert.equal(show(and(A, and(B, C))), 'A ∧ (B ∧ C)');
  assert.equal(show(imp(and(A, B), and(B, A))), '(A ∧ B) → (B ∧ A)');
  assert.equal(show(and(and(A, B), C)), '(A ∧ B) ∧ C');
  assert.equal(show(not(and(A, B))), '¬(A ∧ B)');
  assert.equal(show(not(not(A))), '¬¬A');
  assert.equal(show(or(not(A), B)), '¬A ∨ B');
  assert.equal(show(BOT), '⊥');
  assert.equal(show(iff(A, or(B, C))), 'A ↔ (B ∨ C)');
});

test('precedence: ¬ tightest, then ∧, ∨, →, ↔', () => {
  assert.equal(parseFormula('¬A ∧ B'), and(not(A), B));
  assert.equal(parseFormula('A ∧ B ∨ C'), or(and(A, B), C));
  assert.equal(parseFormula('A ∨ B ∧ C'), or(A, and(B, C)));
  assert.equal(parseFormula('A ∨ B → C'), imp(or(A, B), C));
  assert.equal(parseFormula('A → B ↔ C'), iff(imp(A, B), C));
  assert.equal(parseFormula('A ↔ B → C'), iff(A, imp(B, C)));
  assert.equal(parseFormula('¬¬A → A'), imp(not(not(A)), A));
});

test('→ is right associative; ∧ and ∨ group to the left', () => {
  assert.equal(parseFormula('A → B → C'), imp(A, imp(B, C)));
  assert.equal(parseFormula('A → B → C → A'), imp(A, imp(B, imp(C, A))));
  assert.equal(parseFormula('A ∧ B ∧ C'), and(and(A, B), C));
  assert.equal(parseFormula('A ∨ B ∨ C'), or(or(A, B), C));
});

test('ASCII input is accepted', () => {
  const cases = [
    ['A&B|-B&A', 'A ∧ B ⊢ B ∧ A'],
    ['A /\\ B |- B /\\ A', 'A ∧ B ⊢ B ∧ A'],
    ['A ^ B |- A', 'A ∧ B ⊢ A'],
    ['A and B |- A', 'A ∧ B ⊢ A'],
    ['~A | B |- A -> B', '¬A ∨ B ⊢ A → B'],
    ['!A \\/ B |- A => B', '¬A ∨ B ⊢ A → B'],
    ['-A or B |- A implies B', '¬A ∨ B ⊢ A → B'],
    ['not A |- A -> _|_', '¬A ⊢ A → ⊥'],
    ['bot |- A', '⊥ ⊢ A'],
    ['false |- A', '⊥ ⊢ A'],
    ['A <-> B |- A -> B', 'A ↔ B ⊢ A → B'],
    ['A <=> B, A iff B |- B', 'A ↔ B, A ↔ B ⊢ B'],
    ['|- p -> (q -> p)', '⊢ p → (q → p)'],
    ['p1 & q2 |- q2', 'p1 ∧ q2 ⊢ q2'],
  ];
  for (const [input, expected] of cases) {
    const s = parseSequent(input);
    assert.equal(showSequent(s.premises, s.goal), expected, input);
  }
});

test('a sequent without ⊢ is a goal with no premises', () => {
  const s = parseSequent('¬(A ∧ ¬A)');
  assert.equal(s.premises.length, 0);
  assert.equal(s.goal, not(and(A, not(A))));
  const t = parseSequent('⊢ A → A');
  assert.equal(t.premises.length, 0);
});

test('round trips: parse(show(f)) and parse(showAscii(f)) give f back', () => {
  const r = rng(7);
  for (let i = 0; i < 500; i++) {
    const f = randomFormula(r, ['A', 'B', 'C', 'p'], 5);
    assert.equal(parseFormula(show(f)), f, show(f));
    assert.equal(parseFormula(showAscii(f)), f, showAscii(f));
  }
});

test('sequent round trips', () => {
  const r = rng(11);
  for (let i = 0; i < 100; i++) {
    const premises = [randomFormula(r, ['A', 'B'], 3), randomFormula(r, ['B', 'C'], 2)];
    const goal = randomFormula(r, ['A', 'B', 'C'], 4);
    const s1 = parseSequent(showSequent(premises, goal));
    assert.deepEqual(s1.premises, premises);
    assert.equal(s1.goal, goal);
    const s2 = parseSequent(showSequent(premises, goal, showAscii));
    assert.deepEqual(s2.premises, premises);
    assert.equal(s2.goal, goal);
  }
});

test('friendly parse errors', () => {
  const bad = {
    'A ∧': /missing after/,
    '(A ∧ B': /never closed/,
    'A ∧ B)': /without a matching/,
    'A B': /connective is missing/,
    '∧ A': /needs a formula on its left/,
    'A ∧ ∨ B': /Two connectives in a row/,
    'A ⊢ B ⊢ C': /only once/,
    'A, B': /separate the premises/,
    'A ⊢': /no goal/,
    'A, , B ⊢ C': /premise is missing/,
    'A # B': /not recognised/,
    '': /Type a sequent/,
    'A ⊢ B, C': /Only one goal/,
    'true ⊢ A': /not part of the course notation/,
  };
  for (const [input, re] of Object.entries(bad)) {
    const r = tryParseSequent(input);
    assert.equal(r.ok, false, input);
    assert.match(r.error, re, input);
  }
  assert.throws(() => parseFormula('A ⊢ B'), ParseError);
});

test('LaTeX printing', () => {
  assert.equal(showLatex(imp(A, imp(B, A))), 'A \\to (B \\to A)');
  assert.equal(showLatex(not(or(A, BOT))), '\\neg (A \\lor \\bot)');
  assert.equal(showLatex(atom('pq')), '\\mathit{pq}');
});

test('atoms are listed once, in order', () => {
  assert.deepEqual(atomsOf([parseFormula('C ∧ (A → B) ∨ A')]), ['A', 'B', 'C']);
});
