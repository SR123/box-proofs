// The exercise library, grouped by game.
//
// To add an exercise, add an entry { id, title, sequent } to a group.
// The sequent may use Unicode (→ ∧ ∨ ¬ ⊥ ⊢) or ASCII (-> & | ~ _|_ |-).
// Set invalid: true for a deliberate "Can you prove it?" exercise that has
// no proof; the app then expects a counterexample.

export const GROUPS = [
  {
    id: 'and', title: 'And-game', game: 'and',
    blurb: 'Only ∧ intro and ∧ elim.',
    exercises: [
      { id: 'and-1', title: 'Swap a conjunction', sequent: 'A ∧ B ⊢ B ∧ A' },
      { id: 'and-2', title: 'Two conjunctions', sequent: 'A ∧ B, B ∧ C ⊢ A ∧ C' },
      { id: 'and-3', title: 'Dig out the parts', sequent: 'C ∧ (A ∧ B) ⊢ A ∧ C' },
      { id: 'and-4', title: 'Regroup to the left', sequent: 'A ∧ (B ∧ C) ⊢ (A ∧ B) ∧ C' },
      { id: 'and-5', title: 'Rotate', sequent: '(A ∧ B) ∧ C ⊢ B ∧ (C ∧ A)' },
      { id: 'and-6', title: 'Use a line twice', sequent: 'A ⊢ A ∧ A' },
      { id: 'and-7', title: 'Mix and match', sequent: 'A ∧ (B ∧ C), B ∧ D ⊢ (A ∧ B) ∧ (D ∧ C)' },
    ],
  },
  {
    id: 'imp', title: 'Implication game', game: 'imp',
    blurb: 'Assumption boxes, → intro, → elim and copying a line.',
    exercises: [
      { id: 'imp-1', title: 'Rain, wet, slippery', sequent: 'R → W, W → S ⊢ R → S' },
      { id: 'imp-2', title: 'One box, one copy', sequent: '⊢ A → (B → A)' },
      { id: 'imp-3', title: 'Three boxes', sequent: '⊢ A → (B → (C → A))' },
      { id: 'imp-4', title: 'Four boxes', sequent: '⊢ P → (Q → (R → (S → P)))' },
      { id: 'imp-5', title: 'Six boxes', sequent: '⊢ A → (B → (C → (D → (E → (F → A)))))' },
      { id: 'imp-6', title: 'Keep an implication', sequent: '⊢ (A → B) → (C → (A → B))' },
      { id: 'imp-7', title: 'Can you prove it?', sequent: '⊢ A → (B → C)', invalid: true },
    ],
  },
  {
    id: 'both', title: 'Both games', game: 'imp',
    blurb: 'The ∧ rules and the → rules together.',
    exercises: [
      { id: 'both-1', title: 'Swap inside an implication', sequent: '⊢ (A ∧ B) → (B ∧ A)' },
      { id: 'both-2', title: 'Chain two implications', sequent: 'A → B, B → C ⊢ A → C' },
      { id: 'both-3', title: 'Uncurry', sequent: 'A → (B → C) ⊢ (A ∧ B) → C' },
      { id: 'both-4', title: 'Curry', sequent: '(A ∧ B) → C ⊢ A → (B → C)' },
      { id: 'both-5', title: 'Swap the assumptions', sequent: 'A → (B → C) ⊢ B → (A → C)' },
    ],
  },
  {
    id: 'not', title: 'Not-game', game: 'not',
    blurb: 'Adds ¬ intro, ¬ elim and contra.',
    exercises: [
      { id: 'not-1', title: 'Double negation in', sequent: 'A ⊢ ¬¬A' },
      { id: 'not-2', title: 'Modus tollens', sequent: 'A → B, ¬B ⊢ ¬A' },
      { id: 'not-3', title: 'No contradiction', sequent: '⊢ ¬(A ∧ ¬A)' },
      { id: 'not-4', title: 'From a contradiction, anything', sequent: 'A, ¬A ⊢ B' },
      { id: 'not-5', title: 'Contraposition', sequent: 'A → B ⊢ ¬B → ¬A' },
    ],
  },
  {
    id: 'or', title: 'Or-game', game: 'or',
    blurb: 'Adds ∨ intro and ∨ elim (proof by cases).',
    exercises: [
      { id: 'or-1', title: 'Add a disjunct', sequent: 'A ⊢ A ∨ B' },
      { id: 'or-2', title: 'Swap a disjunction', sequent: 'A ∨ B ⊢ B ∨ A' },
      { id: 'or-3', title: 'Regroup a disjunction', sequent: 'A ∨ (B ∨ C) ⊢ (A ∨ B) ∨ C' },
      { id: 'or-4', title: 'Proof by cases', sequent: 'A ∨ B, A → C, B → C ⊢ C' },
      { id: 'or-5', title: 'Distribute ∧ over ∨', sequent: 'A ∧ (B ∨ C) ⊢ (A ∧ B) ∨ (A ∧ C)' },
      { id: 'or-6', title: 'From ¬A ∨ B to A → B', sequent: '¬A ∨ B ⊢ A → B' },
    ],
  },
  {
    id: 'classical', title: 'Classical', game: 'full',
    blurb: 'These need contra (classical): assume ¬X and reach ⊥.',
    exercises: [
      { id: 'cl-1', title: 'Double negation out', sequent: '¬¬A ⊢ A' },
      { id: 'cl-2', title: 'Excluded middle', sequent: '⊢ A ∨ ¬A' },
      { id: 'cl-3', title: "Peirce's law", sequent: '⊢ ((A → B) → A) → A' },
      { id: 'cl-4', title: 'De Morgan', sequent: '¬(A ∧ B) ⊢ ¬A ∨ ¬B' },
      { id: 'cl-5', title: 'Implication as a disjunction', sequent: 'A → B ⊢ ¬A ∨ B' },
    ],
  },
];

export const EXERCISES = GROUPS.flatMap((g) => g.exercises.map((e) => ({ ...e, group: g.id, game: e.game || g.game })));

export function findExercise(id) {
  return EXERCISES.find((e) => e.id === id) || null;
}
