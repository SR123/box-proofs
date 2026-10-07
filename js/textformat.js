// Plain-text proofs: writing them out with box-drawing characters, and
// reading them back in (for "Check a proof").
//
//   A → (B → A)
//
//        ┌──────────────
//     1  │ A               assumption
//        │ ┌────────────
//     2  │ │ B             assumption
//     3  │ │ A             line 1
//        │ └────────────
//     4  │ B → A           → intro 2–3
//        └──────────────
//     5  A → (B → A)       → intro 1–4
//
// When reading, each numbered line may start with │ or | marks (one per
// box level); the justification is recognised at the end of the line.

import { show, showSequent, parseFormula, parseSequent, ParseError } from './formula.js';
import { layoutRows, justificationText } from './proof.js';

export function proofToText(p, { header = true } = {}) {
  const { rows, boxes, nb } = layoutRows(p);
  const numW = Math.max(2, String(nb.count).length);
  const formulaW = Math.max(8, ...rows.map((r) => 2 * r.depth + (r.kind === 'gap' ? 1 : show(r.line.f).length)));
  const lead = ' '.repeat(numW + 2);
  const bars = (d) => '│ '.repeat(d);
  const border = (d, ch) => lead + bars(d - 1) + ch + '─'.repeat(Math.max(3, formulaW - 2 * (d - 1) - 1));
  const out = [];
  if (header) out.push(showSequent(p.premises, p.goal), '');
  rows.forEach((r, i) => {
    boxes.filter((b) => b.startRow === i).sort((a, b) => a.depth - b.depth).forEach((b) => out.push(border(b.depth, '┌')));
    if (r.kind === 'gap') out.push((lead + bars(r.depth) + '⋮').trimEnd());
    else {
      const f = show(r.line.f);
      const just = r.line.rule === null ? '(goal)' : justificationText(r.line, nb);
      const body = bars(r.depth) + f;
      out.push(String(r.num).padStart(numW) + '  ' + body.padEnd(formulaW) + '   ' + just);
    }
    boxes.filter((b) => b.endRow === i).sort((a, b) => b.depth - a.depth).forEach((b) => out.push(border(b.depth, '└')));
  });
  return out.join('\n');
}

// ---------------------------------------------------------------------------
// Reading

const CONN = {
  and: '∧|&&|&|\\/\\\\|\\^|and|conj',
  or: '∨|\\|\\||\\||\\\\\\/|or|disj|v',
  imp: '→|-->|->|=>|⇒|imp(?:lies|l)?',
  not: '¬|~|!|-|not|neg',
  iff: '↔|<->|<=>|⇔|iff',
};
const REFS = '\\d+(?:\\s*[–—-]\\s*\\d+)?(?:\\s*,\\s*\\d+(?:\\s*[–—-]\\s*\\d+)?)*';
const KIND = '(intro(?:duction)?|elim(?:ination)?|i|e)';

const PATTERNS = [
  [/\s(premise|premiss|prem)\.?$/i, () => ({ rule: 'premise', refs: '' })],
  [/\s(assumption|assume|ass|hyp|hypothesis)\.?$/i, () => ({ rule: 'assumption', refs: '' })],
  [new RegExp(`\\s(?:line|copy|reit(?:eration)?|repeat|rep)\\.?\\s*(${REFS})$`, 'i'), (m) => ({ rule: 'copy', refs: m[1] })],
  [new RegExp(`\\scontra\\s*\\(\\s*classical\\s*\\)\\s*(${REFS})$`, 'i'), (m) => ({ rule: 'raa', refs: m[1] })],
  [new RegExp(`\\s(?:raa|pbc|reductio)\\s*(${REFS})$`, 'i'), (m) => ({ rule: 'raa', refs: m[1] })],
  [new RegExp(`\\s(?:contra(?:\\s*\\(\\s*constructive\\s*\\))?|(?:⊥|bot|_\\|_)\\s*-?\\s*e(?:lim)?|efq)\\s*(${REFS})$`, 'i'), (m) => ({ rule: 'contra', refs: m[1] })],
  ...Object.entries(CONN).map(([c, alt]) => [
    new RegExp(`\\s(?:${alt})\\s*-?\\s*${KIND}\\.?\\s*(${REFS})$`, 'i'),
    (m) => ({ rule: c + (/^i/i.test(m[1]) ? 'I' : 'E'), refs: m[2] }),
  ]),
];

function parseRefs(s) {
  if (!s || !s.trim()) return [];
  return s.split(',').map((part) => {
    const t = part.trim();
    const m = /^(\d+)\s*[–—-]\s*(\d+)$/.exec(t);
    if (m) return [Number(m[1]), Number(m[2])];
    return Number(t);
  });
}

function splitJustification(rest) {
  const s = ' ' + rest.trim();
  for (const [re, make] of PATTERNS) {
    const m = re.exec(s);
    if (m) {
      const r = make(m);
      return { formulaText: s.slice(0, m.index).trim(), rule: r.rule, refs: parseRefs(r.refs) };
    }
  }
  return null;
}

// Returns { sequent, lines, errors }.  lines are in the checker's flat form.
export function parseProofText(text) {
  const errors = [];
  const lines = [];
  let sequent = null;
  const src = String(text).replace(/\r\n?/g, '\n').split('\n');
  src.forEach((raw, idx) => {
    const lineNo = idx + 1;
    const t = raw.replace(/\t/g, '    ').trimEnd();
    if (!t.trim()) return;
    if (/^[\s│|┌└├─┐┘╭╰+⋮:.\-]*$/.test(t)) return; // a box border or a gap
    const m = /^\s*(\d+)\s*[.:)]?\s+(.*)$/.exec(t);
    if (!m) {
      if (!sequent && lines.length === 0) {
        const s = t.replace(/^\s*[A-Za-z ]+:\s*/, '');
        try {
          sequent = parseSequent(s);
          return;
        } catch (e) {
          if (!(e instanceof ParseError)) throw e;
          errors.push({ line: lineNo, message: `The first line should be the sequent (or a numbered line): ${e.message}` });
          return;
        }
      }
      errors.push({ line: lineNo, message: `This text line does not start with a line number: "${t.trim()}".` });
      return;
    }
    const num = Number(m[1]);
    let rest = m[2];
    let depth = 0;
    for (;;) {
      const b = /^\s*[│|┃]\s?/.exec(rest);
      if (!b) break;
      depth++;
      rest = rest.slice(b[0].length);
    }
    // An open goal, as written by "Copy as text" for an unfinished proof.
    const goalMark = /\s+(?:\(goal\)|\?)\s*$/.exec(' ' + rest);
    if (goalMark) {
      const formulaText = (' ' + rest).slice(0, goalMark.index).trim();
      try {
        lines.push({ num, depth, f: parseFormula(formulaText), rule: null, refs: [] });
      } catch (e) {
        if (!(e instanceof ParseError)) throw e;
        errors.push({ line: lineNo, message: `Line ${num}: ${e.message}` });
      }
      return;
    }
    const split = splitJustification(rest);
    if (!split) {
      errors.push({ line: lineNo, message: `Line ${num}: no justification found at the end (for example "premise", "∧ elim 1" or "→ intro 2–4").` });
      return;
    }
    if (!split.formulaText) {
      errors.push({ line: lineNo, message: `Line ${num}: the formula is missing.` });
      return;
    }
    let f;
    try {
      f = parseFormula(split.formulaText);
    } catch (e) {
      if (!(e instanceof ParseError)) throw e;
      errors.push({ line: lineNo, message: `Line ${num}: ${e.message}` });
      return;
    }
    lines.push({ num, depth, f, rule: split.rule, refs: split.refs });
  });
  return { sequent, lines, errors };
}
