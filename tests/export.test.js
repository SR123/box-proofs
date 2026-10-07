import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseSequent } from '../js/formula.js';
import { proveSequent } from '../js/prover.js';
import { newProof, applyMove, openGoals, listMoves, toFlat, layoutRows, fromFlat } from '../js/proof.js';
import { checkProof } from '../js/checker.js';
import { proofToText, parseProofText } from '../js/textformat.js';
import { proofToTikz, proofToSvg } from '../js/export.js';
import { EXERCISES } from '../js/exercises.js';

const VALID = EXERCISES.filter((e) => !e.invalid);

function proofOf(ex) {
  const { premises, goal } = parseSequent(ex.sequent);
  return { premises, goal, proof: proveSequent(premises, goal, ex.game).proof };
}

test('Copy as text: the text reads back and passes the checker', () => {
  for (const ex of VALID) {
    const { premises, goal, proof } = proofOf(ex);
    const text = proofToText(proof);
    const parsed = parseProofText(text);
    assert.deepEqual(parsed.errors, [], ex.id);
    assert.deepEqual(parsed.sequent.premises, premises);
    assert.equal(parsed.sequent.goal, goal);
    const c = checkProof(parsed.lines, parsed.sequent);
    assert.ok(c.ok, `${ex.id}: ${JSON.stringify(c.errors)}`);
    // And it can be loaded into the editor again.
    const back = fromFlat(premises, goal, parsed.lines);
    assert.equal(proofToText(back), text, ex.id);
  }
});

test('Copy as text draws boxes with │ ┌ └', () => {
  const ex = EXERCISES.find((e) => e.id === 'imp-2');
  const text = proofToText(proofOf(ex).proof);
  assert.match(text, /┌/);
  assert.match(text, /└/);
  assert.match(text, /│ │ A +line 1/);
  assert.match(text, /→ intro 1–4/);
});

test('a partial proof shows its gaps', () => {
  const { premises, goal } = parseSequent('⊢ A → (B → A)');
  const p0 = newProof(premises, goal);
  const p1 = applyMove(p0, listMoves(p0, openGoals(p0)[0].id, 'imp')[0]).proof;
  const text = proofToText(p1);
  assert.match(text, /⋮/);
  assert.match(text, /\(goal\)/);
});

test('LaTeX export: a self-contained TikZ picture with nested boxes', () => {
  for (const ex of VALID) {
    const { proof } = proofOf(ex);
    const tex = proofToTikz(proof);
    assert.match(tex, /\\begin\{tikzpicture\}/);
    assert.match(tex, /\\end\{tikzpicture\}$/);
    const boxes = layoutRows(proof).boxes.length;
    assert.equal((tex.match(/rectangle/g) || []).length, boxes, ex.id);
    const lines = toFlat(proof).length;
    assert.equal((tex.match(/anchor=base east/g) || []).length, lines, ex.id);
    assert.ok(!/[∧∨→¬⊥↔–]/.test(tex.split('\n').slice(2).join('\n')), `${ex.id}: Unicode left in the TikZ body`);
  }
});

test('SVG export: well formed, one rectangle per box plus the background', () => {
  for (const ex of VALID) {
    const { proof } = proofOf(ex);
    const svg = proofToSvg(proof);
    assert.match(svg, /^<svg xmlns="http:\/\/www.w3.org\/2000\/svg"/);
    assert.match(svg, /<\/svg>$/);
    const boxes = layoutRows(proof).boxes.length;
    assert.equal((svg.match(/<rect /g) || []).length, boxes + 1, ex.id);
    assert.equal((svg.match(/<text /g) || []).length - (svg.match(/⋮/g) || []).length, toFlat(proof).length * 3, ex.id);
  }
});
