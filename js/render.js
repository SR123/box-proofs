// Drawing a proof as nested boxes on a CSS grid: line numbers on the left,
// formulas indented by box depth, and an aligned justification column.

import { showHtml, speak, escapeHtml } from './formula.js';
import { layoutRows, justificationText } from './proof.js';

const SPOKEN = { '∧': 'and', '∨': 'or', '→': 'implies', '¬': 'not', '↔': 'if and only if', '–': ' to ' };

export function speakJustification(text) {
  return text.replace(/[∧∨→¬↔–]/g, (c) => SPOKEN[c] || c).replace(/\s+/g, ' ');
}

// opts: { currentGoal, selected: Set, visible: Set|null,
//         problems: Map goal id -> status ({ classical } for a goal that
//         needs contra (classical), otherwise a dead end),
//         highlight: Set, focusId, flash: bool (newest lines flash once) }
export function renderProof(proof, opts = {}) {
  const { rows, boxes, nb } = layoutRows(proof);
  const selected = opts.selected || new Set();
  const highlight = opts.highlight || new Set();
  const problems = opts.problems || new Map();
  const chipOf = (id) => {
    const st = problems.get(id);
    if (!st) return null;
    return st.classical ? { cls: 'classical', text: 'needs classical', spoken: 'needs contra (classical)' } : { cls: 'dead', text: 'dead end', spoken: 'dead end' };
  };
  const el = document.createElement('div');
  el.className = 'proof';
  el.setAttribute('role', 'listbox');
  el.setAttribute('aria-label', 'Proof lines. Use the arrow keys to move, Enter to select.');
  el.setAttribute('aria-multiselectable', 'true');
  if (opts.stack) el.classList.add('stack');
  el.style.gridTemplateRows = rows.map((r) => (r.kind === 'gap' ? 'minmax(var(--gap-h), auto)' : 'minmax(var(--row-h), auto)')).join(' ');

  for (const b of boxes) {
    const d = document.createElement('div');
    d.className = 'box' + (b.newest ? ' newest' : '');
    d.style.gridRow = `${b.startRow + 1} / ${b.endRow + 2}`;
    d.style.setProperty('--d', b.depth);
    d.setAttribute('aria-hidden', 'true');
    el.appendChild(d);
  }

  let focusable = null;
  const goalRow = rows.findIndex((r) => r.kind === 'line' && r.line.id === opts.currentGoal);
  rows.forEach((r, i) => {
    const row = document.createElement('div');
    row.style.gridRow = String(i + 1);
    row.style.setProperty('--d', r.depth);
    if (r.kind === 'gap') {
      row.className = 'row gap' + (r.goalId === opts.currentGoal ? ' cur' : '');
      row.dataset.goal = String(r.goalId);
      row.setAttribute('aria-hidden', 'true');
      row.innerHTML = '<span class="num"></span><span class="fm">⋮</span><span class="just"></span>';
      el.appendChild(row);
      return;
    }
    const l = r.line;
    const isGoal = l.rule === null;
    const chip = isGoal ? chipOf(l.id) : null;
    const cls = ['row', isGoal ? 'goal' : 'line'];
    if (isGoal && l.id === opts.currentGoal) cls.push('cur');
    if (chip) cls.push(chip.cls);
    if (!isGoal && selected.has(l.id)) cls.push('sel');
    // Lines above the goal that it cannot use are inside closed boxes: fade them.
    // Lines below the goal are simply not usable for it.
    if (!isGoal && opts.visible && !opts.visible.has(l.id)) cls.push(goalRow >= 0 && i > goalRow ? 'after' : 'out');
    if (l.newest) cls.push('newest');
    if (l.newest && opts.flash) cls.push('flash');
    if (highlight.has(l.id)) cls.push('hl');
    row.className = cls.join(' ');
    row.dataset.id = String(l.id);
    row.dataset.kind = isGoal ? 'goal' : 'line';
    row.setAttribute('role', 'option');
    row.setAttribute('aria-selected', String(isGoal ? l.id === opts.currentGoal : selected.has(l.id)));
    row.tabIndex = -1;
    const just = isGoal ? '' : justificationText(l, nb);
    const spoken = isGoal
      ? `Line ${r.num}: open goal ${speak(l.f)}${chip ? ', ' + chip.spoken : ''}`
      : `Line ${r.num}: ${speak(l.f)}, ${speakJustification(just)}${opts.visible && !opts.visible.has(l.id) ? ', not usable for the selected goal' : ''}`;
    row.setAttribute('aria-label', spoken);
    const justHtml = isGoal
      ? `<span class="chip">${chip ? chip.text : 'goal'}</span>`
      : `<span class="jtext${l.refs.length ? ' has-refs' : ''}" data-line="${l.id}">${escapeHtml(just)}</span>`;
    row.innerHTML = `<span class="num">${r.num}</span><span class="fm"><span class="f">${showHtml(l.f)}</span></span><span class="just">${justHtml}</span>`;
    if (l.id === opts.focusId) focusable = row;
    el.appendChild(row);
  });
  if (!focusable) {
    focusable = el.querySelector('.row.goal.cur') || el.querySelector('.row[role="option"]');
  }
  if (focusable) focusable.tabIndex = 0;
  return el;
}
