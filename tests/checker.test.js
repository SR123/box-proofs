import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseProofText } from '../js/textformat.js';
import { checkProof } from '../js/checker.js';
import { parseSequent } from '../js/formula.js';
import { rulesOf } from '../js/games.js';

// Parse a proof written as text and check it.
function check(text, sequent = null, options = {}) {
  const parsed = parseProofText(text);
  assert.deepEqual(parsed.errors, [], 'the test proof should parse');
  const seq = sequent ? parseSequent(sequent) : parsed.sequent;
  return checkProof(parsed.lines, seq, options);
}

function ok(text, sequent) {
  const r = check(text, sequent);
  assert.equal(r.ok, true, JSON.stringify(r.errors, null, 1));
}

function bad(text, sequent, re, line = null) {
  const r = check(text, sequent);
  assert.equal(r.ok, false, 'expected the checker to reject the proof');
  const hit = r.errors.find((e) => re.test(e.message) && (line === null || e.line === line));
  assert.ok(hit, `expected an error matching ${re}${line ? ` on line ${line}` : ''}; got ${JSON.stringify(r.errors)}`);
}

// ---------------------------------------------------------------------------
// Proofs in the style of the lecture slides.

test('and-game: A ∧ B ⊢ B ∧ A', () => ok(`
1 A ∧ B      premise
2 B          ∧ elim 1
3 A          ∧ elim 1
4 B ∧ A      ∧ intro 2,3`, 'A ∧ B ⊢ B ∧ A'));

test('and-game: the same line used twice', () => ok(`
1 A          premise
2 A ∧ A      ∧ intro 1,1`, 'A ⊢ A ∧ A'));

test('implication game: ⊢ A → (B → A) with a copy', () => ok(`
1 | A                assumption
2 | | B              assumption
3 | | A              line 1
4 | B → A            → intro 2–3
5 A → (B → A)        → intro 1–4`, '⊢ A → (B → A)'));

test('implication game: box-drawing characters are accepted', () => ok(`
⊢ A → (B → A)
    ┌──────────
 1  │ A               assumption
    │ ┌────────
 2  │ │ B             assumption
 3  │ │ A             line 1
    │ └────────
 4  │ B → A           → intro 2–3
    └──────────
 5  A → (B → A)       → intro 1–4`));

test('implication game: R → W, W → S ⊢ R → S', () => ok(`
1 R → W      premise
2 W → S      premise
3 | R        assumption
4 | W        → elim 3,1
5 | S        → elim 4,2
6 R → S      → intro 3–5`, 'R → W, W → S ⊢ R → S'));

test('both games: A → (B → C) ⊢ (A ∧ B) → C', () => ok(`
1 A → (B → C)    premise
2 | A ∧ B        assumption
3 | A            ∧ elim 2
4 | B → C        → elim 3,1
5 | B            ∧ elim 2
6 | C            → elim 5,4
7 (A ∧ B) → C    → intro 2–6`, 'A → (B → C) ⊢ (A ∧ B) → C'));

test('not-game: modus tollens', () => ok(`
1 A → B      premise
2 ¬B         premise
3 | A        assumption
4 | B        → elim 3,1
5 | ⊥        ¬ elim 4,2
6 ¬A         ¬ intro 3–5`, 'A → B, ¬B ⊢ ¬A'));

test('not-game: contra', () => ok(`
1 A          premise
2 ¬A         premise
3 ⊥          ¬ elim 1,2
4 B          contra 3`, 'A, ¬A ⊢ B'));

test('or-game: A ∨ B ⊢ B ∨ A', () => ok(`
1 A ∨ B      premise
2 | A        assumption
3 | B ∨ A    ∨ intro 2
4 | B        assumption
5 | B ∨ A    ∨ intro 4
6 B ∨ A      ∨ elim 1,2–3,4–5`, 'A ∨ B ⊢ B ∨ A'));

test('or-game: a one-line case box', () => ok(`
1 ¬A ∨ B         premise
2 | A            assumption
3 | | ¬A         assumption
4 | | ⊥          ¬ elim 2,3
5 | | B          contra 4
6 | | B          assumption
7 | B            ∨ elim 1,3–5,6–6
8 A → B          → intro 2–7`, '¬A ∨ B ⊢ A → B'));

test('classical: ¬¬A ⊢ A by contra (classical)', () => ok(`
1 ¬¬A                premise
2 | ¬A               assumption
3 | ⊥                ¬ elim 2,1
4 A                  contra (classical) 2–3`, '¬¬A ⊢ A'));

test('classical: excluded middle', () => ok(`
1 | ¬(A ∨ ¬A)        assumption
2 | | A              assumption
3 | | A ∨ ¬A         ∨ intro 2
4 | | ⊥              ¬ elim 3,1
5 | ¬A               ¬ intro 2–4
6 | A ∨ ¬A           ∨ intro 5
7 | ⊥                ¬ elim 6,1
8 A ∨ ¬A             contra (classical) 1–7`, '⊢ A ∨ ¬A'));

test('↔ intro and ↔ elim', () => ok(`
1 A ↔ B          premise
2 A → B          ↔ elim 1
3 B → A          ↔ elim 1
4 B ↔ A          ↔ intro 3,2`, 'A ↔ B ⊢ B ↔ A'));

test('ASCII justifications are accepted', () => ok(`
1 A & B      premise
2 B          &E 1
3 A          and elim 1
4 B & A      /\\ intro 2,3`, 'A ∧ B ⊢ B ∧ A'));

test('a premise may be the conclusion', () => ok(`
1 A          premise`, 'A ⊢ A'));

// ---------------------------------------------------------------------------
// Wrong proofs.

test('spot the bug: a line inside a closed box is out of bounds', () => bad(`
1 | A          assumption
2 A → A        → intro 1–1
3 A            line 1`, '⊢ A', /inside the box 1–1.*out of bounds/, 3));

test('a reference to a later line', () => bad(`
1 A ∧ B      premise
2 B ∧ A      ∧ intro 3,4
3 B          ∧ elim 1
4 A          ∧ elim 1`, 'A ∧ B ⊢ B ∧ A', /comes after line 2/, 2));

test('a reference to a missing line', () => bad(`
1 A ∧ B      premise
2 B          ∧ elim 7`, 'A ∧ B ⊢ B', /no line 7/, 2));

test('∧ elim on a line that is not a conjunction', () => bad(`
1 A → B      premise
2 A          ∧ elim 1`, 'A → B ⊢ A', /needs a conjunction/, 2));

test('∧ intro that does not match its lines', () => bad(`
1 A          premise
2 B          premise
3 B ∧ B      ∧ intro 1,2`, 'A, B ⊢ B ∧ B', /line 1 must be B/i, 3));

test('∧ intro with the lines in the wrong order', () => bad(`
1 A          premise
2 B          premise
3 A ∧ B      ∧ intro 2,1`, 'A, B ⊢ A ∧ B', /wrong order/, 3));

test('→ elim with the lines the wrong way round', () => bad(`
1 A → B      premise
2 A          premise
3 B          → elim 1,2`, 'A → B, A ⊢ B', /→ elim 2,1/, 3));

test('→ intro whose box does not fit', () => bad(`
1 | A          assumption
2 | A ∧ A      ∧ intro 1,1
3 A → A        → intro 1–2`, '⊢ A → A', /gives A → \(A ∧ A\)/, 3));

test('→ intro that does not come straight after its box', () => bad(`
1 B            premise
2 | A          assumption
3 | B          line 1
4 B            line 1
5 A → B        → intro 2–3`, 'B ⊢ A → B', /straight after/));

test('a box that is never closed', () => bad(`
1 B            premise
2 | A          assumption
3 | B          line 1
4 B            line 1`, 'B ⊢ B', /never closed/));

test('a proof that ends inside a box', () => bad(`
1 | A          assumption
2 | A ∧ A      ∧ intro 1,1`, '⊢ A ∧ A', /ends inside a box/));

test('→ intro given a single line instead of a box', () => bad(`
1 A            premise
2 B → A        → intro 1`, 'A ⊢ B → A', /no box from line 1 to line 1/, 2));

test('a premise after other lines', () => bad(`
1 A ∧ B      premise
2 A          ∧ elim 1
3 C          premise`, 'A ∧ B, C ⊢ A', /premises must all come first/, 3));

test('a premise that is not in the sequent', () => bad(`
1 A          premise`, 'B ⊢ A', /not a premise/));

test('the last line is not the goal', () => bad(`
1 A ∧ B      premise
2 A          ∧ elim 1`, 'A ∧ B ⊢ B', /goal is B/));

test('contra with a line that is not ⊥', () => bad(`
1 A          premise
2 B          contra 1`, 'A ⊢ B', /needs a line with ⊥/, 2));

test('¬ intro whose box does not end in ⊥', () => bad(`
1 B            premise
2 | A          assumption
3 | B          line 1
4 ¬A           ¬ intro 2–3`, 'B ⊢ ¬A', /must end with ⊥/, 4));

test('contra (classical) with the wrong assumption', () => bad(`
1 ¬A           premise
2 | A          assumption
3 | ⊥          ¬ elim 2,1
4 A            contra (classical) 2–3`, '¬A ⊢ A', /must assume ¬A/, 4));

test('∨ elim whose boxes assume the wrong formulas', () => bad(`
1 A ∨ B      premise
2 | B        assumption
3 | B ∨ A    ∨ intro 2
4 | A        assumption
5 | B ∨ A    ∨ intro 4
6 B ∨ A      ∨ elim 1,2–3,4–5`, 'A ∨ B ⊢ B ∨ A', /first box must assume A/, 6));

test('∨ intro with a line that is neither side', () => bad(`
1 C          premise
2 A ∨ B      ∨ intro 1`, 'C ⊢ A ∨ B', /neither side/, 2));

test('copying a line with another formula', () => bad(`
1 A          premise
2 | B        assumption
3 | B        line 1
4 B → B      → intro 2–3`, 'A ⊢ B → B', /copying it cannot give B/, 3));

test('a rule outside the current game', () => {
  const parsed = parseProofText(`
1 A          premise
2 A ∨ B      ∨ intro 1`);
  const r = checkProof(parsed.lines, parseSequent('A ⊢ A ∨ B'), { rules: rulesOf('imp') });
  assert.equal(r.ok, false);
  assert.match(r.errors[0].message, /not available/);
});

test('indentation without an assumption', () => bad(`
1 A          premise
2 | A        line 1
3 A          line 1`, 'A ⊢ A', /no box is open/));

test('an open goal is not a complete proof', () => {
  const r = checkProof([{ depth: 0, f: parseSequent('⊢ A').goal, rule: null, refs: [] }], parseSequent('⊢ A'));
  assert.equal(r.ok, false);
  assert.match(r.errors[0].message, /open goal/);
});
