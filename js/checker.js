// An independent checker for complete box proofs.
//
// It works on a flat list of lines, so it does not trust the editor's
// tree structure.  Each line is
//   { depth, f, rule, refs }      refs: line numbers or [first, last] ranges
// Boxes are recovered from the depths: an assumption line opens a box at its
// depth, and the box runs until the depth drops below it or another
// assumption opens a new box at the same depth.

import { BOT, show } from './formula.js';
import { RULE_NAME } from './proof.js';

const DASH = '–';
const S = (f) => show(f);

// Expected reference shapes: 'l' = a line, 'b' = a box.
const SHAPES = {
  premise: '', assumption: '', copy: 'l', andI: 'll', andE: 'l', impI: 'b', impE: 'll',
  notI: 'b', notE: 'll', orI: 'l', orE: 'lbb', contra: 'l', raa: 'b', iffI: 'll', iffE: 'l',
};

const USAGE = {
  copy: 'line k (copy line k)', andI: '∧ intro i,j', andE: '∧ elim i', impI: '→ intro i–j',
  impE: '→ elim i,j', notI: '¬ intro i–j', notE: '¬ elim i,j', orI: '∨ intro i',
  orE: '∨ elim i,j–k,l–m', contra: 'contra i', raa: 'contra (classical) i–j',
  iffI: '↔ intro i,j', iffE: '↔ elim i',
};

const isPrefix = (a, b) => a.length <= b.length && a.every((x, k) => x === b[k]);

// Check a proof.  sequent = { premises, goal } (optional).
// options.rules: a Set of allowed rule ids (optional).
// Returns { ok, errors: [{ line, message }] }.
export function checkProof(lines, sequent = null, options = {}) {
  const errors = [];
  const err = (line, message) => errors.push({ line, message });
  const n = lines.length;
  if (n === 0) return { ok: false, errors: [{ line: 0, message: 'The proof is empty.' }] };

  lines.forEach((l, i) => {
    if (l.num != null && l.num !== i + 1) err(i + 1, `Line numbers must run 1, 2, 3, … (line ${i + 1} is numbered ${l.num}).`);
  });

  // Recover the boxes.
  const boxes = []; // { start, end, parentPath }
  const pathOf = [null]; // pathOf[i] = indices of the boxes containing line i, outermost first
  const stack = [];
  for (let i = 1; i <= n; i++) {
    const l = lines[i - 1];
    const d = Number.isInteger(l.depth) && l.depth >= 0 ? l.depth : 0;
    if (l.rule === 'assumption') {
      if (d === 0) err(i, 'An assumption must open a box; it cannot stand outside all boxes.');
      while (stack.length > 0 && stack.length >= d) boxes[stack.pop()].end = i - 1;
      if (stack.length < d - 1) err(i, `Line ${i} is nested more deeply than the boxes around it.`);
      boxes.push({ start: i, end: null, parentPath: stack.slice() });
      stack.push(boxes.length - 1);
    } else {
      while (stack.length > d) boxes[stack.pop()].end = i - 1;
      if (stack.length < d) err(i, `Line ${i} is indented as if it were inside a box, but no box is open here (a box must start with an assumption).`);
    }
    pathOf[i] = stack.slice();
  }
  while (stack.length) boxes[stack.pop()].end = n;

  const F = (k) => lines[k - 1].f;
  const rangeText = (b) => `${b.start}${DASH}${b.end}`;

  // Why is line k not usable at line i?  Returns a message or null.
  const lineProblem = (k, i) => {
    if (!Number.isInteger(k) || k < 1 || k > n) return `there is no line ${k}`;
    if (k === i) return `line ${i} cannot use itself`;
    if (k > i) return `line ${k} comes after line ${i}; a line may only use lines above it`;
    if (!isPrefix(pathOf[k], pathOf[i])) {
      const closed = pathOf[k].find((b) => !pathOf[i].includes(b));
      const B = boxes[closed];
      return `line ${k} is inside the box ${rangeText(B)}, which is already closed, so line ${k} is out of bounds here (the box rule)`;
    }
    if (lines[k - 1].rule == null) return `line ${k} is an open goal`;
    return null;
  };

  // Find the box with this range; returns its index or a message.
  const findBox = (r, i) => {
    let [a, b] = r;
    const bi = boxes.findIndex((x) => x.start === a && x.end === b);
    if (bi < 0) {
      const starts = boxes.filter((x) => x.start === a);
      if (starts.length) return { msg: `the box that starts at line ${a} ends at line ${starts[0].end}, not at line ${b}` };
      return { msg: `there is no box from line ${a} to line ${b} (a box starts with an assumption)` };
    }
    const B = boxes[bi];
    if (B.end >= i) return { msg: `the box ${a}${DASH}${b} is not closed before line ${i}` };
    if (!isPrefix(B.parentPath, pathOf[i])) return { msg: `the box ${a}${DASH}${b} is inside another box that is already closed (the box rule)` };
    return { bi };
  };

  let seenNonPremise = false;
  const closedBoxes = new Set();

  for (let i = 1; i <= n; i++) {
    const l = lines[i - 1];
    const f = l.f;
    const rule = l.rule;
    const at = (m) => err(i, `Line ${i}: ${m}`);
    if (rule == null) { at('this is still an open goal, so the proof is not finished.'); seenNonPremise = true; continue; }
    if (!(rule in SHAPES)) { at(`"${rule}" is not a rule of the course.`); seenNonPremise = true; continue; }
    if (options.rules && !options.rules.has(rule)) at(`${RULE_NAME[rule]} is not available with the current rules.`);

    if (rule === 'premise') {
      if (pathOf[i].length > 0) at('a premise cannot be inside a box.');
      if (seenNonPremise) at('premises must all come first, before any other line.');
      if (sequent && !sequent.premises.includes(f)) at(`${S(f)} is not a premise of the sequent.`);
      continue;
    }
    seenNonPremise = true;
    if (rule === 'assumption') continue;

    // Reference shapes.
    const shape = SHAPES[rule];
    const refs = l.refs || [];
    if (refs.length !== shape.length) {
      at(`${RULE_NAME[rule]} needs ${describeShape(shape)}; write it as "${USAGE[rule]}".`);
      continue;
    }
    const L = [];
    const B = [];
    let bad = false;
    for (let j = 0; j < shape.length; j++) {
      let r = refs[j];
      if (shape[j] === 'l') {
        if (Array.isArray(r)) {
          if (r[0] === r[1]) r = r[0];
          else { at(`${RULE_NAME[rule]} needs a single line here, not the range ${r[0]}${DASH}${r[1]}.`); bad = true; break; }
        }
        const p = lineProblem(r, i);
        if (p) { at(p + '.'); bad = true; break; }
        L.push(r);
      } else {
        if (!Array.isArray(r)) r = [r, r]; // "→ intro 3" for a one-line box 3–3
        const res = findBox(r, i);
        if (res.msg) { at(res.msg + '.'); bad = true; break; }
        B.push(boxes[res.bi]);
        B[B.length - 1].index = res.bi;
      }
    }
    if (bad) continue;

    const box = B[0];
    const adjacent = (bx) => bx.end === i - 1 && pathOf[i].length === bx.parentPath.length;

    switch (rule) {
      case 'copy':
        if (F(L[0]) !== f) at(`line ${L[0]} is ${S(F(L[0]))}, so copying it cannot give ${S(f)}.`);
        break;
      case 'andI': {
        const [x, y] = L;
        if (f.t !== 'and') { at(`∧ intro gives a conjunction X ∧ Y, but this line is ${S(f)}.`); break; }
        if (F(x) === f.a && F(y) === f.b) break;
        if (F(x) === f.b && F(y) === f.a) { at(`the lines are in the wrong order: for ${S(f)} write ∧ intro ${y},${x}.`); break; }
        at(`∧ intro ${x},${y} gives ${showBin('∧', F(x), F(y))}, not ${S(f)}. Line ${x} must be ${S(f.a)} and line ${y} must be ${S(f.b)}.`);
        break;
      }
      case 'andE': {
        const c = F(L[0]);
        if (c.t !== 'and') { at(`∧ elim needs a conjunction, but line ${L[0]} is ${S(c)}.`); break; }
        if (f !== c.a && f !== c.b) at(`from ${S(c)}, ∧ elim gives ${S(c.a)} or ${S(c.b)}, not ${S(f)}.`);
        break;
      }
      case 'impI': {
        const A = F(box.start);
        const C = F(box.end);
        if (f.t !== 'imp') { at(`→ intro gives an implication, but this line is ${S(f)}.`); break; }
        if (f.a !== A || f.b !== C) at(`the box ${rangeText(box)} assumes ${S(A)} and ends with ${S(C)}, so → intro gives ${showImp(A, C)}, not ${S(f)}.`);
        else if (!adjacent(box)) at(closeMsg('→ intro', box));
        break;
      }
      case 'impE': {
        const [x, xy] = L;
        const I = F(xy);
        if (I.t === 'imp' && I.a === F(x) && I.b === f) break;
        const J = F(x);
        if (J.t === 'imp' && J.a === F(xy) && J.b === f) { at(`write the line with X first and the line with X → Y second: → elim ${xy},${x}.`); break; }
        if (I.t !== 'imp') { at(`→ elim ${x},${xy} needs line ${xy} to be an implication X → Y, but it is ${S(I)}.`); break; }
        if (I.a !== F(x)) { at(`line ${xy} is ${S(I)}, so line ${x} must be ${S(I.a)}, but it is ${S(F(x))}.`); break; }
        at(`from ${S(F(x))} and ${S(I)}, → elim gives ${S(I.b)}, not ${S(f)}.`);
        break;
      }
      case 'notI': {
        const A = F(box.start);
        const C = F(box.end);
        if (f.t !== 'not') { at(`¬ intro gives a negation, but this line is ${S(f)}.`); break; }
        if (C !== BOT) { at(`for ¬ intro the box ${rangeText(box)} must end with ⊥, but it ends with ${S(C)}.`); break; }
        if (f.a !== A) { at(`the box assumes ${S(A)}, so ¬ intro gives ¬${wrapNeg(A)}, not ${S(f)}.`); break; }
        if (!adjacent(box)) at(closeMsg('¬ intro', box));
        break;
      }
      case 'notE': {
        const [a, na] = L;
        if (f !== BOT) { at(`¬ elim gives ⊥, but this line is ${S(f)}.`); break; }
        const X = F(a);
        const Y = F(na);
        if (Y.t === 'not' && Y.a === X) break;
        if (X.t === 'not' && X.a === Y) { at(`write the line with A first and the line with ¬A second: ¬ elim ${na},${a}.`); break; }
        at(`¬ elim ${a},${na} needs line ${a} to be some A and line ${na} to be ¬A, but they are ${S(X)} and ${S(Y)}.`);
        break;
      }
      case 'orI': {
        const X = F(L[0]);
        if (f.t !== 'or') { at(`∨ intro gives a disjunction, but this line is ${S(f)}.`); break; }
        if (f.a !== X && f.b !== X) at(`line ${L[0]} is ${S(X)}, which is neither side of ${S(f)}.`);
        break;
      }
      case 'orE': {
        const D = F(L[0]);
        const [b1, b2] = B;
        if (D.t !== 'or') { at(`∨ elim needs a disjunction, but line ${L[0]} is ${S(D)}.`); break; }
        if (F(b1.start) !== D.a) { at(`the first box must assume ${S(D.a)} (the left side of line ${L[0]}), but it assumes ${S(F(b1.start))}.`); break; }
        if (F(b2.start) !== D.b) { at(`the second box must assume ${S(D.b)} (the right side of line ${L[0]}), but it assumes ${S(F(b2.start))}.`); break; }
        if (F(b1.end) !== f) { at(`the first box must end with ${S(f)}, but it ends with ${S(F(b1.end))}.`); break; }
        if (F(b2.end) !== f) { at(`the second box must end with ${S(f)}, but it ends with ${S(F(b2.end))}.`); break; }
        if (!(adjacent(b2) && b1.end === b2.start - 1 && b1.parentPath.length === b2.parentPath.length)) {
          at(`∨ elim must come straight after its two boxes, and the second box must follow the first one directly.`);
        }
        break;
      }
      case 'contra':
        if (F(L[0]) !== BOT) at(`contra needs a line with ⊥, but line ${L[0]} is ${S(F(L[0]))}.`);
        break;
      case 'raa': {
        const A = F(box.start);
        const C = F(box.end);
        if (C !== BOT) { at(`for contra (classical) the box ${rangeText(box)} must end with ⊥, but it ends with ${S(C)}.`); break; }
        if (A.t !== 'not' || A.a !== f) { at(`for contra (classical) the box must assume ¬${wrapNeg(f)}, but it assumes ${S(A)}.`); break; }
        if (!adjacent(box)) at(closeMsg('contra (classical)', box));
        break;
      }
      case 'iffI': {
        const [x, y] = L;
        if (f.t !== 'iff') { at(`↔ intro gives a biconditional, but this line is ${S(f)}.`); break; }
        const X = F(x);
        const Y = F(y);
        if (!(X.t === 'imp' && Y.t === 'imp' && X.a === f.a && X.b === f.b && Y.a === f.b && Y.b === f.a)) {
          at(`↔ intro ${x},${y} needs line ${x} to be ${showImp(f.a, f.b)} and line ${y} to be ${showImp(f.b, f.a)}.`);
        }
        break;
      }
      case 'iffE': {
        const X = F(L[0]);
        if (X.t !== 'iff') { at(`↔ elim needs a biconditional, but line ${L[0]} is ${S(X)}.`); break; }
        const ok = f.t === 'imp' && ((f.a === X.a && f.b === X.b) || (f.a === X.b && f.b === X.a));
        if (!ok) at(`from ${S(X)}, ↔ elim gives ${showImp(X.a, X.b)} or ${showImp(X.b, X.a)}.`);
        break;
      }
      default:
        break;
    }
    // Record boxes closed here (only when adjacent).
    if (rule === 'orE') {
      const [b1, b2] = B;
      if (adjacent(b2) && b1.end === b2.start - 1) { closedBoxes.add(b1.index); closedBoxes.add(b2.index); }
    } else if (box && adjacent(box)) closedBoxes.add(box.index);
  }

  boxes.forEach((b, bi) => {
    if (closedBoxes.has(bi)) return;
    const next = b.end + 1;
    const text = `The box ${rangeText(b)} is never closed. A box can only be closed by → intro, ¬ intro, ∨ elim or contra (classical), on the line straight after it.`;
    // Avoid repeating an error already reported for the closing line.
    if (!errors.some((e) => e.line === next && /box/.test(e.message))) err(Math.min(next, n), text);
  });

  if (pathOf[n].length > 0) err(n, `The proof ends inside a box. The last line must be the conclusion, outside all boxes.`);
  else if (sequent && F(n) !== sequent.goal) err(n, `The last line is ${S(F(n))}, but the goal is ${S(sequent.goal)}.`);

  errors.sort((a, b) => a.line - b.line);
  return { ok: errors.length === 0, errors };
}

function describeShape(shape) {
  const words = { l: 'a line', b: 'a box i–j' };
  const parts = [...shape].map((c) => words[c]);
  if (parts.length === 1) return parts[0];
  return parts.slice(0, -1).join(', ') + ' and ' + parts[parts.length - 1];
}

function wrapNeg(f) {
  const s = show(f);
  return f.t === 'atom' || f.t === 'bot' || f.t === 'not' ? s : `(${s})`;
}

function showBin(op, a, b) {
  const w = (x) => (['and', 'or', 'imp', 'iff'].includes(x.t) ? `(${show(x)})` : show(x));
  return `${w(a)} ${op} ${w(b)}`;
}

const showImp = (a, b) => showBin('→', a, b);

function closeMsg(name, box) {
  return `${name} must come straight after the box it closes: the box ends at line ${box.end}, so this should be line ${box.end + 1}, just outside the box.`;
}
