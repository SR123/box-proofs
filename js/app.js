// Box proofs: the user interface.

import {
  BOT, not, show, showHtml, showSequent, showSequentHtml, tryParseSequent, escapeHtml, atomsOf,
} from './formula.js';
import {
  newProof, cloneProof, locate, listMoves, applyMove, openGoals, visibleLines, numbering,
  toFlat, fromFlat, isComplete, referencedLineIds, moveResult, layoutRows, forEachItem, contextOf, moveKey,
} from './proof.js';
import { checkProof } from './checker.js';
import { truthTable, evaluate, showAssignment } from './semantics.js';
import { provableI, OracleTimeout } from './intuitionistic.js';
import {
  GAMES, gameById, gameIndex, minimalGame, atLeast, normaliseGameId, rulesOf, isClassical, gameForRules,
} from './games.js';
import { GROUPS, EXERCISES, findExercise } from './exercises.js';
import {
  labelMoves, choiceInfo, moveTitle, moveEffect, explainMove, explainDeadEnd, deadReason, hintText,
  planAll, planFirstStep, goalProblems, markWithPlan, RULE_OF_MOVE,
} from './guide.js';
import { decide } from './prover.js';
import { renderProof } from './render.js';
import { proofToText, parseProofText } from './textformat.js';
import { proofToTikz, proofToSvg } from './export.js';
import { helpHtml } from './help.js';

const $ = (sel) => document.querySelector(sel);
const H = (f) => `<span class="f">${showHtml(f)}</span>`;
const root = document.documentElement;

// ---------------------------------------------------------------------------
// Conveniences kept in localStorage (always optional).

const store = {
  get(key, fallback = null) {
    try {
      const v = localStorage.getItem('boxproofs.' + key);
      return v === null ? fallback : JSON.parse(v);
    } catch (e) {
      return fallback;
    }
  },
  set(key, value) {
    try { localStorage.setItem('boxproofs.' + key, JSON.stringify(value)); } catch (e) { /* ignore */ }
  },
  remove(key) {
    try { localStorage.removeItem('boxproofs.' + key); } catch (e) { /* ignore */ }
  },
};

// "Start afresh": forget the ✓ marks, the typed sequent and the Guided
// setting. Display settings (Present, text size, colour theme) are kept.
function forgetProgress() {
  ['solved', 'own', 'guided', 'last'].forEach((k) => store.remove(k));
}

// The address of the start page: this page without any query string.
function startPageUrl() {
  return location.origin + location.pathname;
}

// ---------------------------------------------------------------------------
// State

const S = {
  premises: [],
  goal: null,
  exerciseId: null,
  title: '',
  game: 'full',
  minGame: 'and',
  proof: null,
  past: [],
  future: [],
  goalId: null,
  sel: new Set(),
  root: { status: 'valid' },
  problems: new Map(), // open goals that cannot be proved: id -> status
  conceal: false,      // a "Can you prove it?" exercise: keep the verdict back
  revealed: false,
  rowGuess: {},
  rowResult: '',
  guided: false,
  guide: { kind: 'idle' },
  guideNote: '',       // a short message above the guide (until the next change)
  whyOpen: new Set(),  // moves whose explanation was opened or closed by hand
  show: null,          // Show me state
  pinned: null,        // line id whose references are shown
  hover: null,
  focusId: null,
  chooser: null,
  embed: false,
  present: false,
  noSolve: false,
  moreOpen: false,
  flashPending: false,
  scrollPending: false,
  version: 0,
  panel: new Map(),    // rule panel entry id -> status, for the phone tray
};

const hidden = () => S.conceal && !S.revealed;

const PANEL = [
  { id: 'andI', label: '∧ intro', rule: 'andI', types: ['andI'] },
  { id: 'impI', label: '→ intro', rule: 'impI', types: ['impI'] },
  { id: 'notI', label: '¬ intro', rule: 'notI', types: ['notI'] },
  { id: 'orIL', label: '∨ intro (left)', rule: 'orI', types: ['orI'], side: 'left' },
  { id: 'orIR', label: '∨ intro (right)', rule: 'orI', types: ['orI'], side: 'right' },
  { id: 'iffI', label: '↔ intro', rule: 'iffI', types: ['iffI'] },
  { id: 'contra', label: 'contra', rule: 'contra', types: ['contra'], secondary: true },
  { id: 'raa', label: 'contra (classical)', rule: 'raa', types: ['raa'], secondary: true },
  { id: 'andE', label: '∧ elim', rule: 'andE', types: ['andE'], fwd: true },
  { id: 'impE', label: '→ elim', rule: 'impE', types: ['impE', 'impEG'], fwd: true },
  { id: 'notE', label: '¬ elim', rule: 'notE', types: ['notE', 'notEG'], fwd: true },
  { id: 'orE', label: '∨ elim', rule: 'orE', types: ['orE'], fwd: true },
  { id: 'iffE', label: '↔ elim', rule: 'iffE', types: ['iffE'], fwd: true },
];

// The label of a rule button; ∨ intro shows the side it keeps.
function entryLabelHtml(entry) {
  if (entry.side && S.goalId !== null && !isComplete(S.proof)) {
    const l = locate(S.proof, S.goalId);
    const G = l && l.item.f;
    if (G && G.t === 'or') return `${escapeHtml(entry.label)}: ${H(entry.side === 'left' ? G.a : G.b)}`;
  }
  return escapeHtml(entry.label);
}

// ---------------------------------------------------------------------------
// Loading a problem

function computeRoot() {
  try {
    return computeRootInner();
  } catch (e) {
    if (e instanceof OracleTimeout) return { status: 'unknown' };
    throw e;
  }
}

function computeRootInner() {
  const deadline = Date.now() + 2000;
  const provable = (ctx, goal) => provableI(ctx, goal, Infinity, deadline);
  const tt = truthTable(S.premises, S.goal);
  if (!tt.tooMany && !tt.valid) return { status: 'invalid', assignment: tt.assignment, atoms: tt.atoms };
  if (tt.tooMany) {
    // Too many atoms for a truth table: Glivenko's theorem turns classical
    // validity into an intuitionistic question.
    if (!provable([...S.premises, not(S.goal)], BOT)) return { status: 'invalid', assignment: null };
    if (!isClassical(S.game) && !provable(S.premises, S.goal)) return { status: 'needsClassical' };
    return { status: 'unknown' };
  }
  if (!isClassical(S.game) && !provable(S.premises, S.goal)) return { status: 'needsClassical' };
  return { status: 'valid' };
}

function loadProblem({ premises, goal, exerciseId = null, title = '', game = null }, opts = {}) {
  stopPlay();
  S.premises = premises;
  S.goal = goal;
  S.exerciseId = exerciseId;
  S.title = title;
  S.minGame = minimalGame(premises, goal);
  S.game = atLeast(game || S.minGame, S.minGame);
  S.proof = newProof(premises, goal);
  S.past = [];
  S.future = [];
  S.sel = new Set();
  S.goalId = openGoals(S.proof)[0]?.id ?? null;
  S.guide = { kind: 'idle' };
  S.guideNote = '';
  S.whyOpen = new Set();
  S.show = null;
  S.chooser = null;
  S.pinned = null;
  S.focusId = null;
  S.root = computeRoot();
  // A "Can you prove it?" exercise keeps its verdict back until asked.
  S.conceal = !!exerciseId && S.root.status === 'invalid';
  S.revealed = false;
  S.rowGuess = Object.fromEntries(atomsOf([...premises, goal]).map((a) => [a, 1]));
  S.rowResult = '';
  if (opts.updateUrl !== false) updateUrl();
  hideTip();
  renderLibrary();
  afterChange();
  if (S.guided) showNextSteps(false);
  S.scrollPending = false;
  render();
}

function loadExercise(id, opts = {}) {
  const ex = findExercise(id);
  if (!ex) return false;
  const r = tryParseSequent(ex.sequent);
  if (!r.ok) return false;
  loadProblem({ premises: r.premises, goal: r.goal, exerciseId: ex.id, title: ex.title, game: opts.game || ex.game }, opts);
  return true;
}

function exerciseGame() {
  const ex = S.exerciseId ? findExercise(S.exerciseId) : null;
  return ex ? ex.game : null;
}

// ---------------------------------------------------------------------------
// Changing the proof

function afterChange() {
  S.problems = S.root.status === 'unknown' ? new Map() : goalProblems(S.proof, S.game);
  if (S.goalId !== null) {
    const l = locate(S.proof, S.goalId);
    if (!l || l.item.k !== 'line' || l.item.rule !== null) S.goalId = null;
  }
  if (S.goalId === null) S.goalId = openGoals(S.proof)[0]?.id ?? null;
  if (isComplete(S.proof) && S.exerciseId) {
    // Solved only with the rules of the exercise's game.
    const ok = checkProof(toFlat(S.proof), { premises: S.premises, goal: S.goal }, { rules: rulesOf(exerciseGame()) }).ok;
    if (ok) {
      const solved = new Set(store.get('solved', []));
      if (!solved.has(S.exerciseId)) {
        solved.add(S.exerciseId);
        store.set('solved', [...solved]);
        renderLibrary();
      }
    }
  }
  S.version++;
}

function commit(proof, { newGoals = [], from = 'user', note = '' } = {}) {
  S.past.push(S.proof);
  if (S.past.length > 300) S.past.shift();
  S.future = [];
  const prevGoal = S.goalId;
  S.proof = proof;
  S.sel = new Set();
  S.chooser = null;
  S.pinned = null;
  S.guideNote = note;
  S.flashPending = true;
  S.scrollPending = true;
  hideTip();
  if (newGoals.length) S.goalId = newGoals[0];
  else {
    const l = locate(proof, prevGoal);
    S.goalId = l && l.item.rule === null ? prevGoal : null;
  }
  if (from !== 'show') { stopPlay(); S.show = null; }
  if (from === 'user' || from === 'guide' || from === 'hint') S.guide = { kind: 'idle' };
  afterChange();
  // After a move from the move list, show the list for the next goal too.
  if ((S.guided || from === 'guide') && from !== 'show' && !isComplete(S.proof)) showNextSteps(false);
  render();
}

function doMove(move, from = 'user', note = '') {
  try {
    const before = S.proof;
    const res = applyMove(S.proof, move);
    commit(res.proof, { newGoals: res.newGoals, from, note: typeof note === 'function' ? note(before) : note });
    announce(`${moveTitle(before, move)} applied.`);
  } catch (e) {
    toast(e.message);
  }
}

function undo() {
  if (!S.past.length) return;
  S.future.push(S.proof);
  S.proof = S.past.pop();
  S.sel = new Set();
  S.chooser = null;
  S.goalId = null;
  S.guideNote = '';
  S.scrollPending = true;
  hideTip();
  if (S.show) { stopPlay(); S.show.index = Math.max(0, S.show.index - 1); if (S.show.index < S.show.steps.length) S.goalId = S.show.steps[S.show.index].move.goalId; } else S.guide = { kind: 'idle' };
  afterChange();
  if (S.guided && !S.show) showNextSteps(false);
  render();
}

function redo() {
  if (!S.future.length) return;
  const next = S.future.pop();
  S.past.push(S.proof);
  S.proof = next;
  S.sel = new Set();
  S.chooser = null;
  S.goalId = null;
  S.guideNote = '';
  S.scrollPending = true;
  hideTip();
  const sh = S.show;
  if (sh && sh.index < sh.steps.length && sh.steps[sh.index].after === next) {
    // Redo during Show me is the next step of Show me.
    sh.index++;
    if (sh.index < sh.steps.length) S.goalId = sh.steps[sh.index].move.goalId;
  } else {
    stopPlay();
    S.show = null;
    S.guide = { kind: 'idle' };
  }
  afterChange();
  if (S.guided && !S.show) showNextSteps(false);
  render();
}

function restart() {
  commit(newProof(S.premises, S.goal));
  S.goalId = openGoals(S.proof)[0]?.id ?? null;
  render();
}

// ---------------------------------------------------------------------------
// Selection

function visibleSet() {
  if (S.goalId === null) return null;
  return new Set(visibleLines(S.proof, S.goalId).map((l) => l.id));
}

function selectGoal(id) {
  if (S.goalId !== id) {
    S.goalId = id;
    S.sel = new Set();
    S.chooser = null;
    S.guideNote = '';
    if (S.guide.kind === 'next' || S.guide.kind === 'hint' || S.guide.kind === 'problem') S.guide = { kind: 'idle' };
    if (S.guided) showNextSteps(false);
  }
  S.focusId = id;
  hideTip();
  render();
}

function toggleLine(id) {
  const vis = visibleSet();
  const nb = numbering(S.proof);
  if (vis && !vis.has(id)) {
    const n = nb.num.get(id);
    const g = nb.num.get(S.goalId);
    const reason = n > g
      ? `Line ${n} comes after the goal on line ${g}, so the goal cannot use it.`
      : `Line ${n} is inside a box that is already closed, so the goal on line ${g} cannot use it (the box rule).`;
    S.focusId = id;
    render();
    showTip(`#proof-scroll .row[data-id="${id}"]`, escapeHtml(reason));
    return;
  }
  if (S.sel.has(id)) S.sel.delete(id);
  else S.sel.add(id);
  S.chooser = null;
  S.focusId = id;
  hideTip();
  render();
}

// ---------------------------------------------------------------------------
// Rule panel

function lineNum(id) {
  return numbering(S.proof).num.get(id);
}

function inconsistentHere() {
  try {
    return decide(contextOf(S.proof, S.goalId), BOT, S.game, Date.now() + 500);
  } catch (e) {
    if (e instanceof OracleTimeout) return null;
    throw e;
  }
}

function panelStatus(entry) {
  if (isComplete(S.proof)) return { moves: [], reason: 'The proof is complete.' };
  if (S.goalId === null) return { moves: [], reason: 'Select an open goal first.' };
  const goal = locate(S.proof, S.goalId).item.f;
  const all = listMoves(S.proof, S.goalId, S.game).filter((m) => entry.types.includes(m.type) && (!entry.side || m.side === entry.side));
  let moves = all;
  const sel = [...S.sel];
  if (entry.fwd && sel.length) moves = all.filter((m) => sel.every((id) => m.lines.includes(id)));
  if (moves.length) return { moves };
  const G = show(goal);
  const vis = visibleLines(S.proof, S.goalId);
  const ofType = (t) => vis.filter((l) => l.f.t === t);
  switch (entry.id) {
    case 'andI': return { moves, reason: `The goal ${G} is not a conjunction X ∧ Y.` };
    case 'impI': return { moves, reason: `The goal ${G} is not an implication X → Y.` };
    case 'notI': return { moves, reason: `The goal ${G} is not a negation ¬X.` };
    case 'iffI': return { moves, reason: `The goal ${G} is not a biconditional X ↔ Y.` };
    case 'orIL': case 'orIR': return { moves, reason: `The goal ${G} is not a disjunction X ∨ Y.` };
    case 'contra': case 'raa': return { moves, reason: 'The goal is already ⊥.' };
    default: break;
  }
  const kind = { andE: ['and', 'conjunction'], impE: ['imp', 'implication'], notE: ['not', 'negation'], orE: ['or', 'disjunction'], iffE: ['iff', 'biconditional'] }[entry.id];
  const cands = ofType(kind[0]);
  if (!cands.length) return { moves, reason: `No line that the goal can use is a ${kind[1]}.` };
  if (sel.length) {
    const wrong = sel.filter((id) => !cands.some((l) => l.id === id));
    if (entry.id === 'impE' && sel.length <= 2 && all.length) return { moves, reason: 'Select a line X → Y, and the line X if you have it.' };
    if (entry.id === 'notE' && all.length) return { moves, reason: 'Select a line ¬X and the line X.' };
    if (wrong.length === sel.length) return { moves, reason: `Line ${lineNum(sel[0])} is not a ${kind[1]}.` };
    if (sel.length > 1 && (entry.id === 'andE' || entry.id === 'orE' || entry.id === 'iffE')) return { moves, reason: `${entry.label} uses one line: select just one.` };
  }
  if (entry.id === 'notE' && goal !== BOT) {
    // Only suggest "contra first" when the ⊥ goal it leaves can be proved.
    if (inconsistentHere() !== false) {
      return { moves, reason: 'You have ¬X but not X. ¬ elim gives ⊥: use contra first so that ⊥ is the goal, then ¬ elim.' };
    }
    if (rulesOf(S.game).has('raa')) {
      return { moves, reason: `¬ elim needs both X and ¬X, but X is not available. contra would leave ⊥ to prove from lines that do not contradict each other, a dead end. Try contra (classical): assume ¬${goal.t === 'atom' || goal.t === 'not' ? G : `(${G})`} and aim for ⊥; then ¬ elim applies.` };
    }
    return { moves, reason: '¬ elim needs both X and ¬X, but X is not available, and the lines above do not contradict each other, so contra would be a dead end.' };
  }
  if (entry.id === 'orE') return { moves, reason: 'One side of each disjunction is already available, so ∨ elim would not help.' };
  return { moves, reason: 'What it would give is already available.' };
}

function choiceHtml(m) {
  const p = S.proof;
  const r = moveResult(p, m);
  const F = (id) => locate(p, id).item.f;
  const n = (id) => lineNum(id);
  switch (m.type) {
    case 'andE': case 'iffE': return `Line ${n(m.lines[0])} gives ${H(r)}`;
    case 'impE': return `Lines ${n(m.lines[0])} and ${n(m.lines[1])} give ${H(r)}`;
    case 'impEG': return `Use ${H(F(m.lines[0]))} (line ${n(m.lines[0])}): first prove ${H(F(m.lines[0]).a)}, then get ${H(r)}`;
    case 'notE': return `Lines ${n(m.lines[0])} and ${n(m.lines[1])} give ⊥`;
    case 'notEG': return `Use ${H(F(m.lines[0]))} (line ${n(m.lines[0])}): prove ${H(F(m.lines[0]).a)} to get ⊥`;
    case 'orE': return `Cases on ${H(F(m.lines[0]))} (line ${n(m.lines[0])})`;
    default: return moveTitle(p, m, true);
  }
}

// Which goal a move would close at once: this one, another one, or none.
function closesBadge(m) {
  const before = openGoals(S.proof).map((g) => g.id);
  const res = applyMove(S.proof, m);
  const after = new Set(openGoals(res.proof).map((g) => g.id));
  if (!after.has(S.goalId) && !res.newGoals.length) return '<span class="tag">closes this goal</span>';
  const other = before.find((id) => id !== S.goalId && !after.has(id));
  if (other) return `<span class="tag other">closes the goal on line ${lineNum(other)}</span>`;
  return '';
}

function clickRule(entry, anchor) {
  const st = panelStatus(entry);
  if (!st.moves.length) {
    const where = anchor && anchor.closest('#tray') ? '#tray' : '#rule-panel';
    if (S.chooser) { S.chooser = null; render(); }
    const el = anchor && anchor.isConnected ? anchor : document.querySelector(`${where} [data-rule="${entry.id}"]`);
    showTip(el, `<b>${escapeHtml(entry.label)}</b>: ${escapeHtml(st.reason)}`);
    return;
  }
  hideTip();
  if (st.moves.length === 1) { doMove(st.moves[0]); return; }
  S.chooser = { entry, moves: st.moves };
  render();
  const first = $('#chooser .opts button');
  if (first) {
    first.focus({ preventScroll: true });
    $('#chooser').scrollIntoView({ block: 'nearest' });
  }
}

// ---------------------------------------------------------------------------
// Guide

function showNextSteps(doRender = true, explicit = false) {
  if (S.goalId === null) { S.guide = { kind: 'idle' }; if (doRender) render(); return; }
  if (hidden()) {
    if (!explicit) { if (doRender) render(); return; }
    S.revealed = true;
  }
  const labelled = labelMoves(S.proof, S.goalId, S.game);
  let planned = null;
  if (S.root.status !== 'invalid') {
    const first = planFirstStep(S.proof, S.goalId, S.game, { timeLimit: 1200 });
    if (first.status === 'ok') {
      planned = first.step.move;
      markWithPlan(labelled, first.plan);
    }
  }
  // Backward moves first, then forward moves; within each, the moves that
  // help come first, then the ones that are safe but not needed, then ✗.
  const rank = (l) => (!l.ok ? 2 : (l.helpful === false || l.roundabout || l.circular) ? 1 : 0);
  labelled.sort((a, b) => (a.move.dir === b.move.dir ? 0 : a.move.dir === 'back' ? -1 : 1) || rank(a) - rank(b));
  S.guide = { kind: 'next', labelled, planned, version: S.version };
  if (doRender) render();
}

function sameMove(a, b) {
  return a && b && a.type === b.type && a.goalId === b.goalId && (a.side || '') === (b.side || '')
    && (a.lines || []).join(',') === (b.lines || []).join(',');
}

function hintDoneNote(before, move) {
  return `<div class="hint-box"><div class="hint-level">Hint 3 of 3: done</div><p>${moveTitle(before, move, true)}. Press <b>Hint</b> again for the next step.</p></div>`;
}

function useHintMove(move) {
  doMove(move, 'hint', (before) => hintDoneNote(before, move));
}

function goalProblemGuide(goalId, info) {
  return { kind: 'problem', goalId, info };
}

function doHint() {
  hideTip();
  if (isComplete(S.proof)) { S.guide = { kind: 'message', html: '<p>The proof is complete. Pick another exercise or type your own sequent.</p>' }; render(); return; }
  const g = S.guide;
  if (hidden()) {
    if (g.kind === 'hint' && g.conceal && g.version === S.version) { S.revealed = true; S.guide = { kind: 'invalid' }; render(); return; }
    S.guide = { kind: 'hint', conceal: true, level: 1, version: S.version, goalId: S.goalId };
    render();
    return;
  }
  if (g.kind === 'hint' && g.version === S.version && g.goalId === S.goalId && g.move) {
    if (g.level >= 2) { useHintMove(g.move); return; }
    S.guide = { ...g, level: g.level + 1 };
    render();
    return;
  }
  if (S.root.status === 'invalid') { S.guide = { kind: 'invalid' }; render(); return; }
  const problem = S.problems.get(S.goalId);
  if (problem) { S.guide = goalProblemGuide(S.goalId, problem); render(); return; }
  const r = planFirstStep(S.proof, S.goalId, S.game, { timeLimit: 1500 });
  if (r.status === 'dead') { S.guide = goalProblemGuide(S.goalId, r.info); render(); return; }
  if (r.status !== 'ok') {
    S.guide = { kind: 'message', html: `<p>${r.status === 'timeout' ? 'The prover ran out of time on this goal. Try a smaller step, or undo.' : 'No hint is available here.'}</p>` };
    render();
    return;
  }
  S.guide = { kind: 'hint', move: r.step.move, level: 1, version: S.version, goalId: S.goalId, circular: r.circular };
  render();
}

function revealIfHidden() {
  if (!hidden()) return false;
  S.revealed = true;
  S.guide = { kind: 'invalid' };
  render();
  return true;
}

function firstProblem() {
  for (const g of openGoals(S.proof)) if (S.problems.has(g.id)) return goalProblemGuide(g.id, S.problems.get(g.id));
  return null;
}

function startShow() {
  hideTip();
  if (S.noSolve) return;
  if (isComplete(S.proof)) { S.guide = { kind: 'message', html: '<p>The proof is already complete. Restart to watch it being built.</p>' }; render(); return; }
  if (revealIfHidden()) return;
  if (S.root.status === 'invalid') { S.guide = { kind: 'invalid' }; render(); return; }
  const problem = firstProblem();
  if (problem) { S.guide = problem; render(); return; }
  const plan = planAll(S.proof, S.game, { timeLimit: 3000 });
  if (plan.status === 'dead') { S.guide = goalProblemGuide(plan.goalId, plan.info); render(); return; }
  if (plan.status !== 'ok') {
    S.guide = { kind: 'message', html: `<p>${plan.status === 'timeout' ? 'The prover reached its time limit, so Show me cannot plan this proof.' : 'Show me could not plan this proof.'}</p>` };
    render();
    return;
  }
  S.show = { steps: plan.steps, index: 0, playing: false, timer: null, choices: new Map() };
  S.guide = { kind: 'show' };
  if (plan.steps.length) S.goalId = plan.steps[0].move.goalId;
  render();
}

function stopShow() {
  stopPlay();
  S.show = null;
  S.guide = { kind: 'idle' };
  render();
}

function stepChoice(i) {
  const sh = S.show;
  if (sh.choices.has(i)) return sh.choices.get(i);
  const step = sh.steps[i];
  const labelled = labelMoves(step.before, step.move.goalId, S.game);
  const info = { labelled, ...choiceInfo(labelled) };
  sh.choices.set(i, info);
  return info;
}

function showNext() {
  const sh = S.show;
  if (!sh || sh.index >= sh.steps.length) return;
  const step = sh.steps[sh.index];
  sh.index++;
  const prevGoal = step.move.goalId;
  S.past.push(S.proof);
  S.future = [];
  S.proof = step.after;
  S.sel = new Set();
  S.flashPending = true;
  S.scrollPending = true;
  const l = locate(S.proof, prevGoal);
  S.goalId = l && l.item.rule === null ? prevGoal : null;
  if (sh.index < sh.steps.length) S.goalId = sh.steps[sh.index].move.goalId;
  afterChange();
  if (sh.index >= sh.steps.length) stopPlay();
  render();
}

function showPrev() {
  const sh = S.show;
  if (!sh || sh.index === 0) return;
  stopPlay();
  S.future.push(S.proof);
  S.proof = S.past.pop();
  sh.index--;
  S.goalId = sh.steps[sh.index].move.goalId;
  S.scrollPending = true;
  afterChange();
  render();
}

function stopPlay() {
  const sh = S.show;
  if (sh && sh.timer) { clearTimeout(sh.timer); sh.timer = null; }
  if (sh) sh.playing = false;
}

function play() {
  const sh = S.show;
  if (!sh) return;
  if (sh.playing) { stopPlay(); render(); return; }
  if (sh.index >= sh.steps.length) return;
  sh.playing = true;
  const tick = (first) => {
    if (!S.show || !S.show.playing) return;
    if (S.show.index >= S.show.steps.length) { stopPlay(); render(); return; }
    // Pause at a choice point (but not on the very first press).
    if (!first && stepChoice(S.show.index).isChoice) { stopPlay(); render(); return; }
    showNext();
    if (S.show) S.show.timer = setTimeout(() => tick(false), reducedMotion() ? 2200 : 1500);
  };
  tick(true);
}

function reducedMotion() {
  try { return window.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (e) { return false; }
}

function finishProof() {
  hideTip();
  if (S.noSolve || isComplete(S.proof)) return;
  if (revealIfHidden()) return;
  if (S.root.status === 'invalid') { S.guide = { kind: 'invalid' }; render(); return; }
  const problem = firstProblem();
  if (problem) { S.guide = problem; render(); return; }
  const plan = planAll(S.proof, S.game, { timeLimit: 3000 });
  if (plan.status === 'dead') { S.guide = goalProblemGuide(plan.goalId, plan.info); render(); return; }
  if (plan.status !== 'ok') {
    S.guide = { kind: 'message', html: `<p>${plan.status === 'timeout' ? 'The prover reached its time limit without finishing.' : 'The prover could not finish this proof.'}</p>` };
    render();
    return;
  }
  // Many lines were added at once, so none is singled out as the newest.
  forEachItem(plan.proof, (it) => { delete it.newest; });
  const n = plan.steps.length;
  commit(plan.proof, { from: 'solve' });
  S.flashPending = false;
  S.guide = { kind: 'message', html: `<p>The prover filled in the remaining ${n} step${n === 1 ? '' : 's'}. Undo takes them back; Restart and Show me let you watch them one by one.</p>` };
  render();
}

function switchGame(id) {
  S.game = atLeast(id, S.minGame);
  S.root = computeRoot();
  S.guide = { kind: 'idle' };
  S.guideNote = '';
  stopPlay();
  S.show = null;
  S.chooser = null;
  updateUrl();
  afterChange();
  if (S.guided) showNextSteps(false);
  render();
}

// ---------------------------------------------------------------------------
// Rendering

function render() {
  renderProblem();
  renderProofPanel();
  renderRules();
  renderGuide();
  renderTray();
  $('#undo-btn').disabled = !S.past.length;
  $('#redo-btn').disabled = !S.future.length;
  $('#solve-btn').disabled = isComplete(S.proof) || (S.root.status === 'invalid' && !hidden());
  $('#solve-btn').hidden = S.noSolve;
  $('#show-btn').hidden = S.noSolve;
  $('#next-btn').disabled = !!S.show;
  if (S.scrollPending) {
    S.scrollPending = false;
    const target = document.querySelector('#proof-scroll .row.goal.cur') || document.querySelector('#proof-scroll .row.newest');
    if (target && typeof target.scrollIntoView === 'function') target.scrollIntoView({ block: 'nearest' });
  }
}

function renderProblem() {
  const g = gameById(S.game);
  $('#game-chip').textContent = g.name;
  $('#problem-title').textContent = S.title || 'Your own sequent';
  $('#sequent').innerHTML = showSequentHtml(S.premises, S.goal);
  $('#sequent').setAttribute('aria-label', 'Sequent: ' + showSequent(S.premises, S.goal));
  const st = $('#problem-status');
  const open = openGoals(S.proof).length;
  if (S.root.status === 'invalid' && !hidden()) st.innerHTML = '<span class="status-pill bad">Not valid</span>';
  else if (S.root.status === 'needsClassical') st.innerHTML = '<span class="status-pill warn">Needs contra (classical)</span>';
  else if (open === 0) st.innerHTML = '<span class="status-pill ok">✓ Proof complete</span>';
  else st.innerHTML = `<span class="status-pill info">${open} open goal${open === 1 ? '' : 's'}</span>`;
  const sel = $('#game-select');
  if (!sel.options.length) {
    for (const gm of GAMES) {
      const o = document.createElement('option');
      o.value = gm.id;
      o.textContent = gm.name;
      sel.appendChild(o);
    }
  }
  for (const o of sel.options) {
    const tooSmall = gameIndex(o.value) < gameIndex(S.minGame);
    o.disabled = tooSmall;
    o.textContent = gameById(o.value).name + (tooSmall ? ' (not enough rules)' : '');
  }
  sel.value = S.game;
  $('#guided-toggle').checked = S.guided;
  $('#more-btn').setAttribute('aria-expanded', String(S.moreOpen));
  $('#tool-more').classList.toggle('open', S.moreOpen);
  document.title = `Box proofs: ${showSequent(S.premises, S.goal)}`;
}

function renderProofPanel() {
  const host = $('#proof-scroll');
  const hadFocus = host.contains(document.activeElement);
  const scrollLeft = host.scrollLeft;
  const hlLine = S.hover ?? S.pinned;
  let highlight = new Set();
  if (hlLine !== null) {
    const l = locate(S.proof, hlLine);
    if (l && l.item.k === 'line') highlight = new Set(referencedLineIds(S.proof, l.item));
  }
  const el = renderProof(S.proof, {
    currentGoal: S.goalId, selected: S.sel, visible: visibleSet(), highlight, focusId: S.focusId,
    problems: hidden() ? new Map() : S.problems, flash: S.flashPending,
  });
  S.flashPending = false;
  host.replaceChildren(el);
  fitProof(host, el);
  host.scrollLeft = scrollLeft;
  if (hadFocus) {
    const target = el.querySelector('.row[tabindex="0"]');
    if (target) target.focus({ preventScroll: true });
  }
  // Selection summary.
  const info = $('#selection-info');
  const nb = numbering(S.proof);
  if (isComplete(S.proof)) info.textContent = '';
  else if (S.goalId === null) info.textContent = 'Select a goal.';
  else {
    const lines = [...S.sel].map((id) => nb.num.get(id)).sort((a, b) => a - b);
    info.textContent = `Goal: line ${nb.num.get(S.goalId)}` + (lines.length ? ` · selected: line${lines.length > 1 ? 's' : ''} ${lines.join(', ')}` : ` · ${touchFirst() ? 'tap' : 'click'} lines above it to use them`);
  }
  // Completion banner.
  const banner = $('#complete-banner');
  if (isComplete(S.proof)) {
    const flat = toFlat(S.proof);
    const seq = { premises: S.premises, goal: S.goal };
    const c = checkProof(flat, seq, { rules: rulesOf(S.game) });
    const exGame = exerciseGame();
    const withinExercise = !exGame || checkProof(flat, seq, { rules: rulesOf(exGame) }).ok;
    const next = nextExercise();
    banner.hidden = false;
    banner.innerHTML = c.ok
      ? `✓ Proof complete. <p>The checker confirms that all ${nb.count} lines follow the rules.${withinExercise ? '' : ` The proof uses rules outside the ${escapeHtml(gameById(exGame).name)}, so the exercise is not marked as solved.`}${next ? ` <button class="btn small" id="next-ex" type="button">Next exercise: ${escapeHtml(next.title)}</button>` : ''}</p>`
      : `The proof has no open goals, but the checker found a problem: ${escapeHtml(c.errors[0].message)}`;
    const nx = $('#next-ex');
    if (nx) nx.addEventListener('click', () => loadExercise(next.id));
  } else banner.hidden = true;
}

function touchFirst() {
  try { return window.matchMedia('(hover: none)').matches; } catch (e) { return false; }
}

// Fit a wide proof into its panel: first shrink it a little; on a phone,
// move the justifications under the formulas; then shrink further (down to
// 72%); beyond that the proof scrolls inside the panel, with a shadow as a hint.
function fitProof(host, el) {
  el.style.removeProperty('--fit');
  el.classList.remove('stack');
  const avail = host.clientWidth - 4;
  if (avail > 0 && el.scrollWidth > avail) {
    const ratio = avail / el.scrollWidth;
    let narrow = false;
    try { narrow = window.matchMedia('(max-width: 640px)').matches; } catch (e) { narrow = false; }
    if (ratio >= 0.85 || !narrow) el.style.setProperty('--fit', Math.max(0.72, ratio).toFixed(3));
    else {
      el.classList.add('stack');
      if (el.scrollWidth > avail) el.style.setProperty('--fit', Math.max(0.72, avail / el.scrollWidth).toFixed(3));
    }
  }
  host.classList.toggle('wide', el.scrollWidth > host.clientWidth + 1);
}

function nextExercise() {
  if (!S.exerciseId) return null;
  const i = EXERCISES.findIndex((e) => e.id === S.exerciseId);
  return i >= 0 && i + 1 < EXERCISES.length ? EXERCISES[i + 1] : null;
}

function currentLabels() {
  return S.guide.kind === 'next' && S.guide.version === S.version ? S.guide.labelled : null;
}

function renderRules() {
  const R = rulesOf(S.game);
  const host = $('#rule-panel');
  const complete = isComplete(S.proof);
  $('#rules-card').classList.toggle('done', complete);
  const groups = [
    { title: 'Work backwards', sub: 'on the goal', items: PANEL.filter((e) => !e.fwd && R.has(e.rule)) },
    { title: 'Work forwards', sub: 'from lines above', items: PANEL.filter((e) => e.fwd && R.has(e.rule)) },
  ];
  const labs = S.guided ? currentLabels() : null;
  host.innerHTML = '';
  S.panel = new Map();
  for (const g of groups) {
    const div = document.createElement('div');
    div.className = 'rule-group';
    div.innerHTML = `<h3>${g.title} <small>${g.sub}</small></h3>`;
    const btns = document.createElement('div');
    btns.className = 'rule-btns';
    for (const e of g.items) {
      const st = panelStatus(e);
      S.panel.set(e.id, st);
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'rule-btn' + (e.secondary && st.moves.length ? ' secondary' : '');
      b.dataset.rule = e.id;
      let mark = '';
      if (labs && st.moves.length) {
        const mine = labs.filter((l) => e.types.includes(l.move.type) && (!e.side || l.move.side === e.side));
        if (mine.some((l) => l.ok)) mark = '<span class="mark ok" aria-hidden="true">✓</span>';
        else if (mine.length) { mark = '<span class="mark bad" aria-hidden="true">✗</span>'; b.classList.add('tint-bad'); }
      }
      b.innerHTML = `<span>${entryLabelHtml(e)}</span>${mark}`;
      if (!st.moves.length) {
        b.setAttribute('aria-disabled', 'true');
        b.title = st.reason;
        b.setAttribute('aria-label', `${e.label}, not available: ${st.reason}`);
      } else {
        b.title = st.moves.length > 1 ? `${e.label}: ${st.moves.length} ways to use it` : moveTitle(S.proof, st.moves[0]);
        if (mark) b.setAttribute('aria-label', `${b.title}, ${mark.includes('✓') ? 'leads to a proof' : 'dead end'}`);
      }
      btns.appendChild(b);
    }
    div.appendChild(btns);
    host.appendChild(div);
  }
  $('#rules-note').textContent = complete
    ? 'The proof is complete.'
    : `${gameById(S.game).name}. Premises, assumptions and copying a line are always allowed.`;
  const ch = $('#chooser');
  if (S.chooser && !complete) {
    ch.hidden = false;
    ch.innerHTML = `<p>${escapeHtml(S.chooser.entry.label)}: which one?</p><div class="opts">${S.chooser.moves.map((m, i) => `<button class="btn" type="button" data-choice="${i}"><span>${choiceHtml(m)}${closesBadge(m)}</span></button>`).join('')}<button class="btn ghost" type="button" data-choice="cancel">Cancel</button></div>`;
  } else {
    ch.hidden = true;
    ch.innerHTML = '';
  }
}

function counterexampleHtml(assignment) {
  const atoms = Object.keys(assignment);
  const v = new Map(atoms.map((a) => [a, !!assignment[a]]));
  const cell = (b) => `<td class="v${b ? 1 : 0}">${b ? 1 : 0}</td>`;
  const head = atoms.map((a) => `<th><i>${escapeHtml(a)}</i></th>`).join('')
    + S.premises.map((p) => `<th>${H(p)}</th>`).join('')
    + `<th class="goalcol">${H(S.goal)}</th>`;
  const g = evaluate(S.goal, v);
  const row = atoms.map((a) => cell(v.get(a))).join('')
    + S.premises.map((p) => cell(evaluate(p, v))).join('')
    + `<td class="goalcol v${g ? 1 : 0}">${g ? 1 : 0}</td>`;
  return `<table class="cx-table"><thead><tr>${head}</tr></thead><tbody><tr>${row}</tr></tbody></table>`;
}

function switchButton() {
  return isClassical(S.game) ? '' : '<div class="guide-actions"><button class="btn small" type="button" data-action="full">Switch to Full rules</button></div>';
}

function rootNotice() {
  if (S.root.status === 'invalid' && !S.root.assignment) {
    return `<div class="notice bad"><h3>✗ Not valid, so there is no proof</h3><p>The sequent is not valid (it has too many atoms to show the counterexample row). Box proofs are sound, so no proof can exist.</p></div>`;
  }
  if (S.root.status === 'invalid') {
    const a = showAssignment(S.root.assignment);
    const P = S.premises.length;
    const lead = a
      ? `With ${escapeHtml(a)}${P ? `, every premise is true but the goal ${H(S.goal)} is false:` : `, the goal ${H(S.goal)} is false:`}`
      : (P ? `Every premise is true but the goal ${H(S.goal)} is false:` : `The goal ${H(S.goal)} is false:`);
    return `<div class="notice bad"><h3>✗ Not valid, so there is no proof</h3>
      <p>${lead}</p>
      ${counterexampleHtml(S.root.assignment)}
      <p>Box proofs are sound: whatever can be proved is true in every row of the truth table. This row is a counterexample, so no box proof can exist.</p></div>`;
  }
  if (S.root.status === 'needsClassical') {
    return `<div class="notice warn"><h3>These rules are not enough</h3>
      <p>The sequent is valid, but it cannot be proved with the rules of the ${escapeHtml(gameById(S.game).name)}: it needs contra (classical), which is only in the Full rules.</p>${switchButton()}</div>`;
  }
  if (S.root.status === 'unknown') {
    return '<div class="notice"><p>This sequent has more than 14 atoms, which is too many for a truth table. The guide still works, but it may be slow.</p></div>';
  }
  return '';
}

function problemNotice(g) {
  const nb = numbering(S.proof);
  const l = locate(S.proof, g.goalId);
  if (!l) return '';
  const f = l.item.f;
  const at = `on line ${nb.num.get(g.goalId) ?? '?'}`;
  if (g.info && g.info.classical) {
    if (S.root.status === 'needsClassical') return ''; // the root notice says it
    return `<div class="notice warn"><h3>Not with these rules</h3><p>The goal ${H(f)} ${at} is true, but proving it would need contra (classical), which is only in the Full rules.${S.past.length ? ' Undo back to the step where it went wrong, or switch to the Full rules.' : ''}</p>${switchButton()}</div>`;
  }
  const reason = deadReason(contextOf(S.proof, g.goalId), f, g.info || {});
  return `<div class="notice bad"><h3>Dead end</h3><p>The goal ${at} cannot be proved. ${reason}${S.past.length ? ' Undo back to the step where it went wrong.' : ''}</p></div>`;
}

function concealPanel() {
  const atoms = Object.keys(S.rowGuess);
  return `<div class="notice puzzle"><h3>Can you prove it?</h3>
    <p>Not every sequent has a proof. Try to build one. If you think there is none, find a row of the truth table in which ${S.premises.length ? 'every premise is true and ' : ''}the goal is false.</p>
    ${atoms.length ? `<div class="row-picker" role="group" aria-label="A row of the truth table">${atoms.map((a) => `<button type="button" data-atom="${escapeHtml(a)}" aria-label="${escapeHtml(a)} is ${S.rowGuess[a]}; click to change"><i>${escapeHtml(a)}</i> = <span class="v${S.rowGuess[a]}">${S.rowGuess[a]}</span></button>`).join('')}</div>` : ''}
    <div class="guide-actions"><button class="btn small" type="button" data-action="check-row">Check this row</button><button class="btn small ghost" type="button" data-action="reveal">Show the answer</button></div>
    ${S.rowResult ? `<p class="row-result">${S.rowResult}</p>` : ''}</div>`;
}

function checkRow() {
  const v = new Map(Object.entries(S.rowGuess).map(([a, x]) => [a, !!x]));
  const row = escapeHtml(showAssignment(S.rowGuess));
  const falsePremise = S.premises.find((p) => !evaluate(p, v));
  if (falsePremise) { S.rowResult = `With ${row} the premise ${H(falsePremise)} is false, so this row is not a counterexample.`; render(); return; }
  if (evaluate(S.goal, v)) { S.rowResult = `With ${row} the goal ${H(S.goal)} is true, so this row is not a counterexample.`; render(); return; }
  S.revealed = true;
  S.rowResult = '';
  S.guide = { kind: 'invalid' };
  S.guideNote = `<div class="notice ok"><h3>✓ Right</h3><p>With ${row}${S.premises.length ? ' every premise is true and' : ''} the goal is false. That row is a counterexample, so no proof can exist.</p></div>`;
  render();
}

function moveItem(lab, i, planned) {
  const p = S.proof;
  const ok = lab.ok;
  const isPlanned = planned && sameMove(planned, lab.move);
  const muted = ok && (lab.helpful === false || lab.roundabout || lab.circular);
  const key = moveKey(lab.move);
  const open = S.whyOpen.has(key) !== !!isPlanned; // the suggested move starts open
  let note = '';
  if (!ok) {
    const fg = locate(lab.after, lab.failing.goalId).item.f;
    note = ` <span class="dead">· dead end: ${H(fg)} cannot be proved${lab.failing.classical ? ' with these rules' : ''}</span>`;
  } else if (lab.circular) note = ' · this goes back to an earlier situation; consider undoing';
  else if (lab.roundabout) note = ' · works, but a direct proof exists';
  else if (lab.helpful === false) note = ' · safe, but the suggested proof does not need it';
  const plain = moveTitle(p, lab.move);
  return `<li class="move ${ok ? 'ok' : 'bad'}${muted ? ' muted' : ''}${isPlanned ? ' planned' : ''}">
    <div class="move-head">
      <span class="badge ${ok ? 'ok' : 'bad'}" role="img" aria-label="${ok ? 'leads to a proof' : 'dead end'}">${ok ? '✓' : '✗'}</span>
      <span class="move-title">${i < 9 ? `<span class="key" aria-hidden="true">${i + 1}</span>` : ''}${moveTitle(p, lab.move, true)}${isPlanned ? '<span class="tag">suggested</span>' : ''}</span>
      <button class="btn small${ok ? '' : ' ghost'}" type="button" data-apply="${i}" aria-label="${ok ? 'Use' : 'Try'} ${escapeHtml(plain)}">${ok ? 'Use' : 'Try it'}</button>
    </div>
    <div class="move-effect">${moveEffect(p, lab.move, lab)}${note} <button class="why" type="button" data-why="${escapeHtml(key)}" aria-expanded="${open}">${open ? 'Hide' : 'Why?'}</button></div>
    ${open ? `<div class="move-why">${explainMove(p, lab.move)}${ok ? '' : ` <span class="dead">${explainDeadEnd(lab)}</span>`}</div>` : ''}
  </li>`;
}

function renderGuide() {
  const body = $('#guide-body');
  const g = S.guide;
  let html = S.guideNote || '';
  const complete = isComplete(S.proof);
  if (g.kind !== 'show') html += hidden() ? (g.kind === 'hint' ? '' : concealPanel()) : rootNotice();
  if (g.kind === 'show' && S.show) {
    html += renderShow();
  } else if (complete) {
    if (g.kind === 'message') html += g.html;
    html += `<div class="done-actions"><p class="muted">Keep this proof:</p><div class="guide-actions">
      <button class="btn small" type="button" data-action="copy-text">Copy as text</button>
      <button class="btn small" type="button" data-action="copy-latex">Copy LaTeX</button>
      <button class="btn small" type="button" data-action="svg">Download SVG</button></div>
      ${S.noSolve ? '' : '<p class="muted">Or watch it being built: <button class="btn small" type="button" data-action="replay">Show me from the start</button></p>'}</div>`;
  } else if (g.kind === 'next' && g.version === S.version) {
    const labelled = g.labelled;
    const nb = numbering(S.proof);
    const goalF = locate(S.proof, S.goalId).item.f;
    const info = choiceInfo(labelled);
    const problem = S.problems.get(S.goalId);
    html += `<p class="lead">Moves for the goal ${H(goalF)} on line ${nb.num.get(S.goalId)}:</p>`;
    if (problem) html += problemNotice(goalProblemGuide(S.goalId, problem));
    else if (!labelled.length || info.good === 0) html += '<p>The guide could not label these moves in time. Try Hint, or undo a step.</p>';
    else if (labelled.every((l) => !l.ok || l.circular) && info.good) html += '<div class="notice warn"><p>Every move that still works goes back to an earlier situation. Consider undoing the last steps.</p></div>';
    else if (info.isChoice) html += `<p class="choice-note">There is a choice: ${info.strategic} different moves lead to a proof. Pick one.</p>`;
    else if (info.good === 1 && labelled.length > 1) html += '<p class="choice-note">Only one of these moves leads to a proof.</p>';
    const back = labelled.map((l, i) => [l, i]).filter(([l]) => l.move.dir === 'back');
    const fwd = labelled.map((l, i) => [l, i]).filter(([l]) => l.move.dir === 'fwd');
    if (back.length) html += `<div class="moves-group"><h3>Work backwards (from the goal)</h3><ul class="move-list">${back.map(([l, i]) => moveItem(l, i, g.planned)).join('')}</ul></div>`;
    if (fwd.length) html += `<div class="moves-group"><h3>Work forwards (from the lines above)</h3><ul class="move-list">${fwd.map(([l, i]) => moveItem(l, i, g.planned)).join('')}</ul></div>`;
  } else if (g.kind === 'hint' && g.version === S.version) {
    if (g.conceal) {
      html += `<div class="hint-box"><div class="hint-level">Hint 1 of 2</div><p>Before you build a proof, ask whether the sequent is valid at all: is there a row of the truth table in which ${S.premises.length ? 'every premise is true and ' : ''}the goal is false?</p></div>
        <div class="guide-actions"><button class="btn" type="button" data-hint="more">Tell me more</button></div>`;
      html += concealPanel();
    } else {
      const level = g.level;
      const text = hintText(S.proof, g.move, level);
      html += `<div class="hint-box"><div class="hint-level">Hint ${level} of 3</div><p>${text}</p></div>
        <div class="guide-actions">${level < 2 ? '<button class="btn" type="button" data-hint="more">Tell me more</button>' : ''}<button class="btn primary" type="button" data-hint="do">Do it</button></div>`;
    }
  } else if (g.kind === 'problem') {
    html += problemNotice(g);
  } else if (g.kind === 'invalid') {
    if (S.root.status !== 'invalid') html += '<p>No hint is available.</p>';
  } else if (g.kind === 'message') {
    html += g.html;
  } else if (!hidden() && (S.root.status === 'valid' || S.root.status === 'unknown')) {
    html += `<p class="muted">Choose a rule for the goal, or ask for help: <b>Hint</b> nudges you in three steps, <b>Moves</b> lists every sensible move and says which ones still lead to a proof${S.noSolve ? '' : ', and <b>Show me</b> builds the proof one step at a time'}.</p>`;
  }
  body.innerHTML = html;
  $('#show-btn').textContent = S.show ? 'Stop' : 'Show me';
  $('#show-btn').setAttribute('aria-pressed', String(!!S.show));
  updateGuideOverflow();
}

// The guide sits next to the proof and scrolls on its own: it is sized to
// the visible part of the window, with a "More below" cue when it overflows.
function updateGuideOverflow() {
  const card = $('#guide-panel');
  const cs = getComputedStyle(card);
  const sticky = cs.position === 'sticky';
  if (sticky) {
    const top = Math.max(card.getBoundingClientRect().top, parseFloat(cs.top) || 0);
    card.style.maxHeight = `${Math.max(260, Math.floor(window.innerHeight - top - 12))}px`;
  } else card.style.removeProperty('max-height');
  card.classList.toggle('more-below', sticky && card.scrollHeight - card.scrollTop - card.clientHeight > 12);
}

function renderShow() {
  const sh = S.show;
  const n = sh.steps.length;
  let html = `<div class="show-controls" role="group" aria-label="Show me controls">
    <button class="btn small" type="button" data-show="prev" ${sh.index === 0 ? 'disabled' : ''}>◀ Previous</button>
    <button class="btn small primary" type="button" data-show="next" ${sh.index >= n ? 'disabled' : ''}>Next ▶</button>
    <button class="btn small" type="button" data-show="play" ${sh.index >= n ? 'disabled' : ''}>${sh.playing ? 'Pause' : 'Play'}</button>
    <span class="step-count">Step ${sh.index} of ${n}</span>
  </div>`;
  if (sh.index > 0) {
    const step = sh.steps[sh.index - 1];
    html += `<div class="hint-box"><div class="hint-level">Step ${sh.index}: ${moveTitle(step.before, step.move, true)}</div><p>${explainMove(step.before, step.move)}</p></div>`;
  } else {
    html += '<p>Press <b>Next</b> to see the first step, or <b>Play</b> to watch them all. Play stops where there is a choice.</p>';
  }
  if (sh.index < n) {
    const next = sh.steps[sh.index];
    const info = stepChoice(sh.index);
    const nb = numbering(next.before);
    const goalF = locate(next.before, next.move.goalId).item.f;
    html += `<p class="lead"><b>Next:</b> ${moveTitle(next.before, next.move, true)} for the goal ${H(goalF)} (line ${nb.num.get(next.move.goalId)}).</p>`;
    const others = info.labelled.filter((l) => !sameMove(l.move, next.move));
    const plannedLab = info.labelled.find((l) => sameMove(l.move, next.move));
    if (info.isChoice) {
      const otherGood = info.strategic - 1;
      html += `<p class="choice-note">This is a choice point: ${info.strategic} moves lead to a proof. Show me takes the one marked below; the other ✓ move${otherGood === 1 ? ' works' : 's work'} too.</p>`;
      const all = plannedLab ? [plannedLab, ...others] : others;
      html += `<details class="moves-group" open><summary>All moves here (${all.filter((o) => o.ok).length} ✓, ${all.filter((o) => !o.ok).length} ✗)</summary><ul class="move-list">${all.map((l) => showItem(next.before, l, l === plannedLab)).join('')}</ul></details>`;
    } else if (others.length) {
      html += `<details class="moves-group"><summary>Other moves here (${others.filter((o) => o.ok).length} ✓, ${others.filter((o) => !o.ok).length} ✗)</summary><ul class="move-list">${others.map((l) => showItem(next.before, l, false)).join('')}</ul></details>`;
    }
  } else {
    html += '<div class="notice ok"><h3>✓ Done</h3><p>That is the whole proof. Use Previous to step back through it, or Restart to try it yourself.</p></div>';
  }
  return html;
}

function showItem(p, lab, taken) {
  return `<li class="move ${lab.ok ? 'ok' : 'bad'}${taken ? ' planned' : ''}">
    <div class="move-head"><span class="badge ${lab.ok ? 'ok' : 'bad'}" role="img" aria-label="${lab.ok ? 'leads to a proof' : 'dead end'}">${lab.ok ? '✓' : '✗'}</span>
    <span class="move-title">${moveTitle(p, lab.move, true)}${taken ? '<span class="tag">taken</span>' : ''}</span></div>
    <div class="move-why">${lab.ok ? explainMove(p, lab.move) : `<span class="dead">${explainDeadEnd(lab)}</span>`}</div>
  </li>`;
}

// Quick actions at the bottom of a phone screen (hidden by CSS elsewhere).
function renderTray() {
  const tray = $('#tray');
  const sh = S.show;
  if (sh) {
    const n = sh.steps.length;
    const cap = sh.index > 0 ? `Step ${sh.index} of ${n}: ${moveTitle(sh.steps[sh.index - 1].before, sh.steps[sh.index - 1].move, true)}` : `${n} steps. Press Next.`;
    tray.innerHTML = `<button class="btn small" type="button" data-show="prev" aria-label="Previous step" ${sh.index === 0 ? 'disabled' : ''}>◀</button>
      <button class="btn small primary" type="button" data-show="next" ${sh.index >= n ? 'disabled' : ''}>Next ▶</button>
      <button class="btn small" type="button" data-show="play" ${sh.index >= n ? 'disabled' : ''}>${sh.playing ? 'Pause' : 'Play'}</button>
      <span class="caption">${cap}</span>`;
    return;
  }
  if (isComplete(S.proof)) {
    const next = nextExercise();
    tray.innerHTML = `<span class="caption done">✓ Proof complete</span>${next ? `<button class="btn small" type="button" data-tray="next-ex">Next exercise</button>` : ''}`;
    return;
  }
  const btns = PANEL.filter((e) => (S.panel.get(e.id) || { moves: [] }).moves.length)
    .map((e) => `<button class="rule-btn${e.secondary ? ' secondary' : ''}" type="button" data-rule="${e.id}"><span>${entryLabelHtml(e)}</span></button>`).join('');
  tray.innerHTML = `<button class="btn small" type="button" data-tray="undo" aria-label="Undo" ${S.past.length ? '' : 'disabled'}><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M9 14 4 9l5-5"/><path d="M4 9h10a6 6 0 0 1 0 12h-3"/></svg></button>
    <button class="btn small" type="button" data-tray="hint">Hint</button>${btns}`;
}

function renderLibrary() {
  const host = $('#library');
  const solved = new Set(store.get('solved', []));
  const current = S.exerciseId ? findExercise(S.exerciseId) : null;
  host.innerHTML = GROUPS.map((g) => {
    const open = current ? current.group === g.id : g === GROUPS[0];
    const done = g.exercises.filter((e) => solved.has(e.id)).length;
    return `<details class="group" ${open ? 'open' : ''} data-group="${g.id}">
      <summary><span>${escapeHtml(g.title)}</span><span class="count" aria-label="${done} of ${g.exercises.length} solved">${done ? `${done}/` : ''}${g.exercises.length}</span></summary>
      <p class="blurb">${escapeHtml(g.blurb)}</p>
      <ul class="ex-list">${g.exercises.map((e) => {
        const r = tryParseSequent(e.sequent);
        const seq = r.ok ? showSequentHtml(r.premises, r.goal) : escapeHtml(e.sequent);
        return `<li><button class="ex-btn" type="button" data-ex="${e.id}" ${S.exerciseId === e.id ? 'aria-current="true"' : ''}>
          <span class="ex-title">${escapeHtml(e.title)}</span><span class="ex-done">${solved.has(e.id) ? '✓' : ''}</span>
          <span class="ex-seq">${seq}</span></button></li>`;
      }).join('')}</ul></details>`;
  }).join('') + `<div class="library-foot">
      <button class="btn small" id="fresh-btn" type="button" aria-describedby="fresh-note">Start afresh</button>
      <p class="blurb" id="fresh-note">Opens the first exercise and clears your ✓ marks.</p>
    </div>`;
}

let freshTimer = null;
// Back to the start page without reloading: the first exercise with an empty
// proof and a plain address. With forget = true, also forget the progress.
function goToStartPage({ forget = false } = {}) {
  if (forget) {
    forgetProgress();
    S.guided = false;
    $('#own-input').value = '';
    updatePreview();
  }
  setDrawer(false);
  loadExercise(EXERCISES[0].id, { updateUrl: false });
  try { history.replaceState(null, '', startPageUrl()); } catch (e) { /* sandbox */ }
  window.scrollTo(0, 0);
  if (forget) toast('Started afresh: your ✓ marks are cleared.', 4000);
}

function onFreshClick(btn) {
  if (btn.dataset.armed === '1') {
    clearTimeout(freshTimer);
    goToStartPage({ forget: true });
    return;
  }
  btn.dataset.armed = '1';
  btn.textContent = 'Click again to start afresh';
  btn.classList.add('armed');
  clearTimeout(freshTimer);
  freshTimer = setTimeout(() => {
    btn.dataset.armed = '';
    btn.textContent = 'Start afresh';
    btn.classList.remove('armed');
  }, 4000);
}

// ---------------------------------------------------------------------------
// Tips, toasts and announcements

let tipTimer = null;
let tipAnchor = null;
function showTip(target, html) {
  const el = typeof target === 'string' ? document.querySelector(target) : target;
  const tip = $('#tip');
  tip.innerHTML = html;
  tip.hidden = false;
  tipAnchor = el;
  placeTip();
  clearTimeout(tipTimer);
  tipTimer = setTimeout(hideTip, 9000);
}
// Put the tip under its anchor (or above it when there is no room); it
// follows the anchor when the page scrolls, and closes when it leaves the view.
function placeTip() {
  const tip = $('#tip');
  const el = tipAnchor;
  tip.style.left = '0px';
  tip.style.top = '0px';
  const vw = window.innerWidth;
  const vh = window.innerHeight;
  const tw = tip.offsetWidth;
  const th = tip.offsetHeight;
  let x = Math.max(8, (vw - tw) / 2);
  let y = vh - th - 90;
  if (el && el.isConnected) {
    const r = el.getBoundingClientRect();
    if (r.bottom < 0 || r.top > vh) { hideTip(); return; }
    x = Math.min(Math.max(8, r.left), vw - tw - 8);
    y = r.bottom + 8;
    if (y + th > vh - 8) y = Math.max(8, r.top - th - 8);
  }
  tip.style.left = `${Math.round(x)}px`;
  tip.style.top = `${Math.round(y)}px`;
}
function hideTip() {
  const tip = $('#tip');
  if (tip && !tip.hidden) tip.hidden = true;
  tipAnchor = null;
}

let toastTimer = null;
function toast(msg, ms = 2600) {
  const t = $('#toast');
  t.textContent = msg;
  t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { t.hidden = true; }, ms);
}
function announce(msg) {
  const live = $('#sr-status');
  live.textContent = '';
  setTimeout(() => { live.textContent = msg; }, 30);
}

// ---------------------------------------------------------------------------
// URLs

const KNOWN = ['s', 'game', 'mode', 'embed', 'ex', 'rules', 'present', 'solve', 'fresh'];

// Read the query string by hand, so that an unencoded "&" inside a sequent
// (as in ?s=A&B|-B&A) still works.
function readParams() {
  const raw = location.search.replace(/^\?/, '');
  const out = {};
  if (!raw) return out;
  const re = new RegExp(`(?:^|&)(${KNOWN.join('|')})=`, 'g');
  const hits = [];
  let m;
  while ((m = re.exec(raw))) hits.push({ key: m[1], start: m.index + m[0].length, at: m.index });
  hits.forEach((h, i) => {
    const end = i + 1 < hits.length ? hits[i + 1].at : raw.length;
    let v = raw.slice(h.start, end);
    try { v = decodeURIComponent(v.replace(/\+/g, ' ')); } catch (e) { /* keep raw */ }
    out[h.key] = v;
  });
  return out;
}

// A short link: an exercise by its id (with the rule set only if it was
// changed), otherwise the sequent itself.
function shareUrl({ embed = S.embed } = {}) {
  const parts = [];
  if (S.exerciseId) {
    parts.push('ex=' + encodeURIComponent(S.exerciseId));
    if (S.game !== exerciseGame()) parts.push('game=' + encodeURIComponent(S.game));
  } else {
    parts.push('s=' + encodeURIComponent(showSequent(S.premises, S.goal)));
    if (S.game !== S.minGame) parts.push('game=' + encodeURIComponent(S.game));
  }
  if (S.guided) parts.push('mode=guided');
  if (S.noSolve) parts.push('solve=0');
  if (embed) parts.push('embed=1');
  return location.origin + location.pathname + '?' + parts.join('&');
}

function updateUrl() {
  try { history.replaceState(null, '', shareUrl()); } catch (e) { /* file:// or sandbox */ }
  const full = $('#open-full');
  if (full) full.href = shareUrl({ embed: false });
}

// ---------------------------------------------------------------------------
// Clipboard and downloads

async function copy(text, what) {
  try {
    await navigator.clipboard.writeText(text);
    toast(`${what} copied.`);
  } catch (e) {
    const d = $('#copy-dialog');
    $('#copy-area').value = text;
    $('#copy-title').textContent = `Copy ${what === 'LaTeX' ? what : what.toLowerCase()}`;
    openDialog(d);
    $('#copy-area').select();
  }
}

function download(name, text, type) {
  try {
    const blob = new Blob([text], { type });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = name;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 2000);
    toast(`${name} downloaded.`);
  } catch (e) {
    copy(text, 'SVG');
  }
}

function fileStem() {
  return (S.exerciseId || 'proof').replace(/[^a-z0-9-]+/gi, '-');
}

// ---------------------------------------------------------------------------
// Dialogs

function openDialog(d) {
  hideTip();
  if (typeof d.showModal === 'function') {
    if (!d.open) d.showModal();
  } else d.setAttribute('open', '');
}
function closeDialog(d) {
  if (typeof d.close === 'function') d.close();
  else d.removeAttribute('open');
}

function openCheckDialog() {
  closeMenus();
  // Prefill with the current proof only when it is finished.
  if (!$('#check-input').value.trim() && isComplete(S.proof)) $('#check-input').value = proofToText(S.proof);
  openDialog($('#check-dialog'));
}

function sameSequent(seq) {
  return seq.goal === S.goal && seq.premises.length === S.premises.length && seq.premises.every((p, i) => p === S.premises[i]);
}

const RULE_WORDS = {
  andI: '∧ intro', andE: '∧ elim', impI: '→ intro', impE: '→ elim', notI: '¬ intro', notE: '¬ elim', contra: 'contra',
  orI: '∨ intro', orE: '∨ elim', raa: 'contra (classical)', iffI: '↔ intro', iffE: '↔ elim',
};

let imported = null;
function runCheck() {
  const text = $('#check-input').value;
  const out = $('#check-result');
  const parsed = parseProofText(text);
  imported = null;
  $('#check-open').hidden = true;
  if (parsed.errors.length) {
    out.innerHTML = `<div class="notice bad"><h3>Could not read the proof</h3><ul class="check-errors">${parsed.errors.map((e) => `<li>${escapeHtml(e.message)}</li>`).join('')}</ul></div>`;
    return;
  }
  if (!parsed.lines.length) {
    out.innerHTML = '<div class="notice bad"><p>No numbered lines found.</p></div>';
    return;
  }
  const seq = parsed.sequent || { premises: S.premises, goal: S.goal };
  const res = checkProof(parsed.lines, seq);
  const seqText = showSequentHtml(seq.premises, seq.goal);
  if (res.ok) {
    // Which rule set does the proof need?
    const used = new Set(parsed.lines.map((l) => l.rule));
    const need = atLeast(gameForRules(used), minimalGame(seq.premises, seq.goal));
    const current = sameSequent(seq) ? S.game : null;
    const beyond = current && gameIndex(need) > gameIndex(current)
      ? [...used].filter((r) => !rulesOf(current).has(r)).map((r) => RULE_WORDS[r] || r)
      : [];
    out.innerHTML = `<div class="notice ok"><h3>✓ Correct</h3><p>This is a valid box proof of ${seqText}: all ${parsed.lines.length} lines follow the rules.${beyond.length ? ` It uses ${escapeHtml(beyond.join(', '))}, which ${beyond.length === 1 ? 'is' : 'are'} not in the ${escapeHtml(gameById(current).name)}; opening it switches the rule set to the ${escapeHtml(gameById(need).name)}.` : ''}</p></div>`;
    imported = { seq, lines: parsed.lines, game: need };
    $('#check-open').hidden = false;
  } else {
    out.innerHTML = `<div class="notice bad"><h3>✗ ${res.errors.length} problem${res.errors.length === 1 ? '' : 's'}</h3><p>Checked against ${seqText}.</p><ul class="check-errors">${res.errors.map((e) => `<li>${escapeHtml(e.message)}</li>`).join('')}</ul></div>`;
  }
}

function openImported() {
  if (!imported) return;
  const { seq, lines, game } = imported;
  if (!sameSequent(seq)) loadProblem({ premises: seq.premises, goal: seq.goal, game });
  else if (gameIndex(game) > gameIndex(S.game)) {
    S.game = game;
    S.root = computeRoot();
    updateUrl();
  }
  const p = fromFlat(seq.premises, seq.goal, lines);
  commit(p);
  S.flashPending = false;
  closeDialog($('#check-dialog'));
  render();
}

// ---------------------------------------------------------------------------
// Own sequent input

function updatePreview() {
  const input = $('#own-input');
  const v = input.value;
  const prev = $('#own-preview');
  const errEl = $('#own-error');
  if (!v.trim()) {
    prev.innerHTML = '';
    errEl.textContent = '';
    input.removeAttribute('aria-invalid');
    return null;
  }
  const r = tryParseSequent(v);
  if (r.ok) {
    prev.innerHTML = `<span class="label">Reads as</span> ${showSequentHtml(r.premises, r.goal)}`;
    errEl.textContent = '';
    input.removeAttribute('aria-invalid');
    return r;
  }
  prev.innerHTML = '';
  const at = r.pos != null && r.pos < v.length ? ` (at “${v.slice(r.pos, r.pos + Math.max(1, r.length || 1))}”, position ${r.pos + 1})` : '';
  errEl.textContent = r.error + at;
  input.setAttribute('aria-invalid', 'true');
  return null;
}

function insertSymbol(sym) {
  const input = $('#own-input');
  const a = input.selectionStart ?? input.value.length;
  const b = input.selectionEnd ?? input.value.length;
  const spaced = ['→', '∧', '∨', '↔', '⊢'].includes(sym) ? ` ${sym} ` : sym;
  const before = input.value.slice(0, a).replace(/ $/, spaced.startsWith(' ') ? '' : ' ');
  let after = input.value.slice(b);
  if (spaced.endsWith(' ')) after = after.replace(/^ +/, '');
  input.value = before + spaced + after;
  const pos = before.length + spaced.length;
  input.focus();
  input.setSelectionRange(pos, pos);
  updatePreview();
}

// ---------------------------------------------------------------------------
// Drawer, Present, theme

function setDrawer(open) {
  const sb = $('#sidebar');
  const drawerMode = root.classList.contains('drawer');
  sb.classList.toggle('open', open && drawerMode);
  $('#scrim').hidden = !(open && drawerMode);
  $('#drawer-btn').setAttribute('aria-expanded', String(open && drawerMode));
  if (open && drawerMode) {
    const cur = sb.querySelector('.ex-btn[aria-current="true"]');
    const target = cur || $('#drawer-close');
    target.focus({ preventScroll: true });
    if (cur) {
      // Keep the top of the drawer in view unless the current exercise is not.
      const r = cur.getBoundingClientRect();
      if (r.bottom > window.innerHeight - 8) cur.scrollIntoView({ block: 'center' });
      else sb.scrollTop = 0;
    }
  }
}

function updateDrawerMode() {
  const on = !S.embed && (S.present || window.innerWidth <= 1100);
  root.classList.toggle('drawer', on);
  if (!on) setDrawer(false);
}

function setPresent(on) {
  S.present = !!on && !S.embed;
  root.classList.toggle('present', S.present);
  store.set('present', S.present);
  $('#present-btn').setAttribute('aria-pressed', String(S.present));
  updateDrawerMode();
  render();
}

const THEME_ICONS = {
  auto: '<svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="8"/><path d="M12 4a8 8 0 0 1 0 16z" class="fill"/></svg>',
  light: '<svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>',
  dark: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M20 14.5A8 8 0 0 1 9.5 4a8 8 0 1 0 10.5 10.5z"/></svg>',
};

function updateThemeButton() {
  const cur = root.dataset.theme || 'auto';
  const b = $('#theme-btn');
  b.innerHTML = THEME_ICONS[cur];
  b.setAttribute('aria-label', `Colour theme: ${cur === 'auto' ? 'automatic' : cur}. Click to change.`);
  b.title = `Colour theme: ${cur === 'auto' ? 'automatic' : cur}`;
}

// ---------------------------------------------------------------------------
// Events

function rowsInOrder() {
  return [...document.querySelectorAll('#proof-scroll .row[role="option"]')];
}

function activateRow(row) {
  const id = Number(row.dataset.id);
  if (row.dataset.kind === 'goal') selectGoal(id);
  else toggleLine(id);
}

function closeMenus() {
  $('#export-menu').open = false;
}

function onShowControl(what) {
  if (!S.show) return;
  if (what === 'next') { stopPlay(); showNext(); } else if (what === 'prev') showPrev();
  else if (what === 'play') { play(); render(); } else if (what === 'stop') stopShow();
}

function guideAction(action) {
  if (action === 'full') switchGame('full');
  else if (action === 'copy-text') copy(proofToText(S.proof), 'Text');
  else if (action === 'copy-latex') copy(proofToTikz(S.proof), 'LaTeX');
  else if (action === 'svg') download(`${fileStem()}.svg`, proofToSvg(S.proof), 'image/svg+xml');
  else if (action === 'replay') { restart(); startShow(); } else if (action === 'check-row') checkRow();
  else if (action === 'reveal') { S.revealed = true; S.guide = { kind: 'invalid' }; render(); }
}

function wire() {
  $('#drawer-btn').addEventListener('click', () => setDrawer(!$('#sidebar').classList.contains('open')));
  $('#drawer-close').addEventListener('click', () => { setDrawer(false); $('#drawer-btn').focus(); });
  $('#scrim').addEventListener('click', () => setDrawer(false));

  $('#home-link').addEventListener('click', (e) => {
    if (e.metaKey || e.ctrlKey || e.shiftKey || e.altKey || e.button !== 0) return;   // new tab etc.
    e.preventDefault();
    goToStartPage();
  });

  $('#library').addEventListener('click', (e) => {
    const fb = e.target.closest('#fresh-btn');
    if (fb) { onFreshClick(fb); return; }
    const b = e.target.closest('[data-ex]');
    if (!b) return;
    loadExercise(b.dataset.ex);
    setDrawer(false);
  });

  $('#own-input').addEventListener('input', updatePreview);
  $('#own-form').addEventListener('submit', (e) => {
    e.preventDefault();
    const r = updatePreview();
    if (!r) {
      if (!$('#own-input').value.trim()) { $('#own-error').textContent = 'Type a sequent first, for example A ∧ B ⊢ B ∧ A.'; }
      $('#own-input').focus();
      return;
    }
    store.set('own', $('#own-input').value);
    loadProblem({ premises: r.premises, goal: r.goal });
    setDrawer(false);
  });
  document.querySelector('.palette').addEventListener('click', (e) => {
    const b = e.target.closest('[data-sym]');
    if (b) insertSymbol(b.dataset.sym);
  });

  // Proof panel: clicks, hover on justifications, keyboard.
  const proofHost = $('#proof-scroll');
  proofHost.addEventListener('click', (e) => {
    const j = e.target.closest('.jtext.has-refs');
    if (j) {
      const id = Number(j.dataset.line);
      S.pinned = S.pinned === id ? null : id;
      renderProofPanel();
      return;
    }
    const gap = e.target.closest('.row.gap');
    if (gap) { selectGoal(Number(gap.dataset.goal)); return; }
    const row = e.target.closest('.row[role="option"]');
    if (row) activateRow(row);
  });
  proofHost.addEventListener('mouseover', (e) => {
    const j = e.target.closest('.jtext.has-refs');
    const id = j ? Number(j.dataset.line) : null;
    if (id !== S.hover) { S.hover = id; renderProofPanel(); }
  });
  proofHost.addEventListener('mouseleave', () => {
    if (S.hover !== null) { S.hover = null; renderProofPanel(); }
  });
  proofHost.addEventListener('focusin', (e) => {
    const row = e.target.closest('.row[role="option"]');
    if (!row) return;
    let keyboard = false;
    try { keyboard = row.matches(':focus-visible'); } catch (err) { keyboard = false; }
    if (!keyboard) return;
    const id = Number(row.dataset.id);
    if (S.focusId !== id || S.pinned !== (row.dataset.kind === 'line' ? id : null)) {
      S.focusId = id;
      const newPinned = row.dataset.kind === 'line' ? id : null;
      if (S.pinned !== newPinned) {
        S.pinned = newPinned;
        // Update highlight classes without rebuilding (keeps focus stable).
        const l = newPinned !== null ? locate(S.proof, newPinned) : null;
        const ids = l ? new Set(referencedLineIds(S.proof, l.item).map(String)) : new Set();
        for (const r of rowsInOrder()) r.classList.toggle('hl', ids.has(r.dataset.id));
      }
    }
  });
  proofHost.addEventListener('keydown', (e) => {
    const row = e.target.closest('.row[role="option"]');
    if (!row) return;
    const rows = rowsInOrder();
    const i = rows.indexOf(row);
    let target = null;
    if (e.key === 'ArrowDown') target = rows[Math.min(rows.length - 1, i + 1)];
    else if (e.key === 'ArrowUp') target = rows[Math.max(0, i - 1)];
    else if (e.key === 'Home') target = rows[0];
    else if (e.key === 'End') target = rows[rows.length - 1];
    else if (e.key === 'Enter' || e.key === ' ') {
      e.preventDefault();
      activateRow(row);
      return;
    } else if (e.key === 'Escape') {
      if (S.sel.size) { S.sel = new Set(); render(); }
      return;
    }
    if (target) {
      e.preventDefault();
      for (const r of rows) r.tabIndex = -1;
      target.tabIndex = 0;
      target.focus();
    }
  });

  // Rules.
  $('#rule-panel').addEventListener('click', (e) => {
    const b = e.target.closest('[data-rule]');
    if (!b) return;
    clickRule(PANEL.find((x) => x.id === b.dataset.rule), b);
  });
  $('#chooser').addEventListener('click', (e) => {
    const b = e.target.closest('[data-choice]');
    if (!b || !S.chooser) return;
    if (b.dataset.choice === 'cancel') { S.chooser = null; render(); return; }
    doMove(S.chooser.moves[Number(b.dataset.choice)]);
  });

  // Phone tray.
  $('#tray').addEventListener('click', (e) => {
    const r = e.target.closest('[data-rule]');
    if (r) { clickRule(PANEL.find((x) => x.id === r.dataset.rule), r); return; }
    const s = e.target.closest('[data-show]');
    if (s) { onShowControl(s.dataset.show); return; }
    const t = e.target.closest('[data-tray]');
    if (!t) return;
    if (t.dataset.tray === 'undo') undo();
    else if (t.dataset.tray === 'hint') { doHint(); $('#guide-panel').scrollIntoView({ block: 'nearest' }); } else if (t.dataset.tray === 'next-ex') { const nx = nextExercise(); if (nx) loadExercise(nx.id); }
  });

  // Toolbar.
  $('#undo-btn').addEventListener('click', undo);
  $('#redo-btn').addEventListener('click', redo);
  $('#restart-btn').addEventListener('click', restart);
  $('#more-btn').addEventListener('click', () => { S.moreOpen = !S.moreOpen; renderProblem(); });
  $('#game-select').addEventListener('change', (e) => switchGame(e.target.value));
  $('#guided-toggle').addEventListener('change', (e) => {
    S.guided = e.target.checked;
    store.set('guided', S.guided);
    updateUrl();
    if (S.guided) showNextSteps();
    else { if (S.guide.kind === 'next') S.guide = { kind: 'idle' }; render(); }
  });
  $('#copy-link').addEventListener('click', () => { closeMenus(); copy(shareUrl({ embed: false }), 'Link'); });
  $('#copy-text').addEventListener('click', () => { closeMenus(); copy(proofToText(S.proof), 'Text'); });
  $('#copy-latex').addEventListener('click', () => { closeMenus(); copy(proofToTikz(S.proof), 'LaTeX'); });
  $('#download-svg').addEventListener('click', () => {
    closeMenus();
    download(`${fileStem()}.svg`, proofToSvg(S.proof), 'image/svg+xml');
  });
  $('#check-menu').addEventListener('click', openCheckDialog);
  document.addEventListener('click', (e) => {
    const menu = $('#export-menu');
    if (menu.open && !menu.contains(e.target)) menu.open = false;
  });
  $('#smaller-btn').addEventListener('click', () => setSize(-1));
  $('#bigger-btn').addEventListener('click', () => setSize(1));

  // Guide.
  $('#hint-btn').addEventListener('click', doHint);
  $('#next-btn').addEventListener('click', () => {
    hideTip();
    if (S.show) return;
    if (isComplete(S.proof)) { S.guide = { kind: 'idle' }; render(); return; }
    showNextSteps(true, true);
  });
  $('#show-btn').addEventListener('click', () => {
    if (S.show) { stopShow(); return; }
    startShow();
  });
  $('#solve-btn').addEventListener('click', finishProof);
  const guideBody = $('#guide-body');
  guideBody.addEventListener('click', (e) => {
    const a = e.target.closest('[data-apply]');
    if (a && S.guide.kind === 'next') { doMove(S.guide.labelled[Number(a.dataset.apply)].move, 'guide'); return; }
    const w = e.target.closest('[data-why]');
    if (w) {
      const k = w.dataset.why;
      if (S.whyOpen.has(k)) S.whyOpen.delete(k); else S.whyOpen.add(k);
      renderGuide();
      const again = [...document.querySelectorAll('#guide-body [data-why]')].find((x) => x.dataset.why === k);
      if (again) again.focus({ preventScroll: true });
      return;
    }
    const h = e.target.closest('[data-hint]');
    if (h && S.guide.kind === 'hint') {
      if (S.guide.conceal) { S.revealed = true; S.guide = { kind: 'invalid' }; render(); return; }
      if (h.dataset.hint === 'do') useHintMove(S.guide.move);
      else { S.guide = { ...S.guide, level: Math.min(2, S.guide.level + 1) }; render(); }
      return;
    }
    const at = e.target.closest('[data-atom]');
    if (at) {
      S.rowGuess[at.dataset.atom] = 1 - S.rowGuess[at.dataset.atom];
      S.rowResult = '';
      renderGuide();
      const again = [...document.querySelectorAll('#guide-body [data-atom]')].find((x) => x.dataset.atom === at.dataset.atom);
      if (again) again.focus({ preventScroll: true });
      return;
    }
    const act = e.target.closest('[data-action]');
    if (act) { guideAction(act.dataset.action); return; }
    const s = e.target.closest('[data-show]');
    if (s) onShowControl(s.dataset.show);
  });
  $('#guide-panel').addEventListener('scroll', updateGuideOverflow, { passive: true });

  // Dialogs.
  $('#help-btn').addEventListener('click', () => openDialog($('#help-dialog')));
  $('#check-btn').addEventListener('click', openCheckDialog);
  $('#check-run').addEventListener('click', runCheck);
  $('#check-current').addEventListener('click', () => { $('#check-input').value = proofToText(S.proof); runCheck(); });
  $('#check-open').addEventListener('click', openImported);
  for (const d of document.querySelectorAll('dialog')) {
    d.addEventListener('click', (e) => {
      if (e.target.closest('[data-close]')) closeDialog(d);
      else if (e.target === d) closeDialog(d); // click on the backdrop
    });
  }

  // Present and theme.
  $('#present-btn').addEventListener('click', () => setPresent(!S.present));
  $('#theme-btn').addEventListener('click', () => {
    const cur = root.dataset.theme || 'auto';
    const next = { auto: 'light', light: 'dark', dark: 'auto' }[cur];
    if (next === 'auto') delete root.dataset.theme;
    else root.dataset.theme = next;
    try { if (next === 'auto') localStorage.removeItem('boxproofs.theme'); else localStorage.setItem('boxproofs.theme', next); } catch (e) { /* ignore */ }
    updateThemeButton();
    toast(`Colour theme: ${next === 'auto' ? 'automatic' : next}`);
  });

  // Tips close on the next click elsewhere, on scrolling and on Escape.
  document.addEventListener('pointerdown', (e) => {
    if (!tipAnchor && $('#tip').hidden) return;
    if (e.target.closest('#tip') || (tipAnchor && tipAnchor.contains(e.target))) return;
    hideTip();
  }, true);
  let scrollFrame = 0;
  window.addEventListener('scroll', () => {
    if (!$('#tip').hidden) placeTip();
    if (!scrollFrame) scrollFrame = requestAnimationFrame(() => { scrollFrame = 0; updateGuideOverflow(); });
  }, { passive: true });

  // Keyboard shortcuts.
  document.addEventListener('keydown', onKey);

  // Refit a wide proof when the window changes size.
  let resizeTimer = null;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      hideTip();
      updateDrawerMode();
      const host = $('#proof-scroll');
      const el = host.querySelector('.proof');
      if (el) fitProof(host, el);
      updateGuideOverflow();
    }, 120);
  });
}

function setSize(delta) {
  const sizes = [0.95, 1.05, 1.15, 1.25, 1.4, 1.6, 1.85, 2.1, 2.4];
  let i = store.get('sizeIndex', null);
  if (i === null) i = window.matchMedia && window.matchMedia('(max-width: 640px)').matches ? 2 : 4;
  i = Math.max(0, Math.min(sizes.length - 1, i + delta));
  store.set('sizeIndex', i);
  root.style.setProperty('--proof-size', sizes[i] + 'rem');
  if (delta !== 0) render();
}

function onKey(e) {
  const t = e.target;
  const typing = t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT' || t.isContentEditable);
  const dialogOpen = [...document.querySelectorAll('dialog')].some((d) => d.open);
  const mod = e.ctrlKey || e.metaKey;
  if (e.key === 'Escape') {
    hideTip();
    if ($('#sidebar').classList.contains('open')) setDrawer(false);
    if ($('#export-menu').open) closeMenus();
    if (S.chooser) { S.chooser = null; render(); }
    return;
  }
  if (typing || dialogOpen) return;
  if (mod && (e.key === 'z' || e.key === 'Z')) {
    e.preventDefault();
    if (e.shiftKey) redo();
    else undo();
    return;
  }
  if (mod && (e.key === 'y' || e.key === 'Y')) { e.preventDefault(); redo(); return; }
  if (mod || e.altKey) return;
  // In Show me, ← and → step through it, wherever the focus is.
  if (S.show && (e.key === 'ArrowRight' || e.key === 'ArrowLeft')) {
    e.preventDefault();
    if (e.key === 'ArrowRight') { stopPlay(); showNext(); } else showPrev();
    return;
  }
  const k = e.key.toLowerCase();
  if (e.key === '?') { e.preventDefault(); openDialog($('#help-dialog')); return; }
  if (k === 'h') { e.preventDefault(); doHint(); return; }
  if (k === 'm' || k === 'n') { e.preventDefault(); $('#next-btn').click(); return; }
  if (k === 's' && !S.noSolve) { e.preventDefault(); $('#show-btn').click(); return; }
  if (k === 'p' && !S.embed) { e.preventDefault(); setPresent(!S.present); return; }
  if (/^[1-9]$/.test(e.key) && S.guide.kind === 'next' && S.guide.version === S.version) {
    const lab = S.guide.labelled[Number(e.key) - 1];
    if (lab) { e.preventDefault(); doMove(lab.move, 'guide'); }
  }
}

// ---------------------------------------------------------------------------
// Start

function start() {
  $('#help-body').innerHTML = helpHtml();
  const params = readParams();
  const fresh = /^(1|true|yes)$/i.test(params.fresh || '');
  store.remove('last');                    // older versions reopened the last problem
  if (fresh) forgetProgress();
  S.embed = /^(1|true|yes)$/i.test(params.embed || '');
  if (S.embed) root.classList.add('embed');
  S.noSolve = /^(0|false|no|off)$/i.test(params.solve || '');
  const mode = (params.mode || '').toLowerCase();
  S.guided = mode === 'guided' || mode === 'guide' || (mode === '' && store.get('guided', false) === true && !S.embed);
  let present = store.get('present', false) === true;
  if (params.present) present = /^(1|true|yes)$/i.test(params.present);
  S.present = present && !S.embed;
  root.classList.toggle('present', S.present);
  $('#present-btn').setAttribute('aria-pressed', String(S.present));
  updateDrawerMode();
  if (store.get('sizeIndex', null) !== null) setSize(0);
  updateThemeButton();
  wire();
  const own = store.get('own', '');
  if (own) { $('#own-input').value = own; updatePreview(); }

  const game = normaliseGameId(params.game || params.rules);
  let loaded = false;
  let missing = null;
  if (params.ex) {
    loaded = loadExercise(params.ex, { game });
    if (!loaded) missing = params.ex;
  }
  if (!loaded && params.s) {
    const r = tryParseSequent(params.s);
    if (r.ok) {
      // A link to an exercise by its sequent shows the exercise title too.
      const ex = EXERCISES.find((x) => { const q = tryParseSequent(x.sequent); return q.ok && q.goal === r.goal && q.premises.length === r.premises.length && q.premises.every((f, i) => f === r.premises[i]); });
      if (ex) loaded = loadExercise(ex.id, { game });
      else { loadProblem({ premises: r.premises, goal: r.goal, game }); loaded = true; }
    } else {
      $('#own-input').value = params.s;
      updatePreview();
      toast('The sequent in the link could not be read: ' + r.error, 5000);
    }
  }
  // A plain address (no ?ex= or ?s=) always opens the start page: the first
  // exercise with an empty proof, so a lecture demo starts the same way every time.
  if (!loaded) loadExercise(EXERCISES[0].id, { updateUrl: !!missing });
  if (fresh) {
    try { history.replaceState(null, '', startPageUrl()); } catch (e) { /* sandbox */ }
    toast('Started afresh: your ✓ marks are cleared.', 4000);
  }
  if (missing) toast(`There is no exercise “${missing}”, so “${S.title}” was opened instead.`, 5000);
  if (mode === 'showme' || mode === 'show') startShow();
}

start();

// Expose a little for tests and the browser console.
window.boxproofs = { state: S, show, cloneProof, layoutRows, atomsOf, RULE_OF_MOVE };
