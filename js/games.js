// The "games" of the course restrict which rules are available.
// They are cumulative: each game adds rules to the previous one.

import { connectivesOf } from './formula.js';

export const GAMES = [
  { id: 'and', name: 'And-game', short: 'And', adds: ['andI', 'andE'] },
  { id: 'imp', name: 'Implication game', short: 'Implication', adds: ['impI', 'impE'] },
  { id: 'not', name: 'Not-game', short: 'Not', adds: ['notI', 'notE', 'contra'] },
  { id: 'or', name: 'Or-game', short: 'Or', adds: ['orI', 'orE'] },
  { id: 'full', name: 'Full rules (classical)', short: 'Full', adds: ['raa', 'iffI', 'iffE'] },
];

const ALIASES = {
  and: 'and', conj: 'and', conjunction: 'and',
  imp: 'imp', implication: 'imp', impl: 'imp', both: 'imp',
  not: 'not', neg: 'not', negation: 'not',
  or: 'or', disj: 'or', disjunction: 'or',
  full: 'full', classical: 'full', all: 'full', raa: 'full',
};

export function normaliseGameId(s) {
  if (!s) return null;
  return ALIASES[String(s).toLowerCase().trim()] || null;
}

export function gameIndex(id) {
  const i = GAMES.findIndex((g) => g.id === id);
  return i < 0 ? GAMES.length - 1 : i;
}

export function gameById(id) {
  return GAMES[gameIndex(id)];
}

// Set of rule ids allowed in a game.  "premise", "assumption" and copying a
// line ("line k") are always allowed.
export function rulesOf(id) {
  const k = gameIndex(id);
  const set = new Set(['premise', 'assumption', 'copy']);
  for (let i = 0; i <= k; i++) for (const r of GAMES[i].adds) set.add(r);
  return set;
}

// The smallest game whose rules cover the connectives of a sequent.
export function minimalGame(premises, goal) {
  const c = connectivesOf([...premises, goal]);
  if (c.has('iff')) return 'full';
  if (c.has('or')) return 'or';
  if (c.has('not') || c.has('bot')) return 'not';
  if (c.has('imp')) return 'imp';
  return 'and';
}

// The smallest game that allows every rule in the set (rule ids as in a proof).
export function gameForRules(rules) {
  for (const g of GAMES) {
    const R = rulesOf(g.id);
    if ([...rules].every((r) => r == null || R.has(r))) return g.id;
  }
  return 'full';
}

export function atLeast(id, min) {
  return gameIndex(id) >= gameIndex(min) ? id : min;
}

export const isClassical = (id) => id === 'full';
