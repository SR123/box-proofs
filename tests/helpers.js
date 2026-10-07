// Shared helpers for the tests.

import { atom, not, and, or, imp, iff, BOT, parseSequent } from '../js/formula.js';

// A small seeded random number generator (mulberry32).
export function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export const pick = (r, xs) => xs[Math.floor(r() * xs.length)];

// A random formula over the given atoms with depth at most `depth`.
export function randomFormula(r, atoms, depth, { iffs = true, bots = true } = {}) {
  if (depth === 0 || r() < 0.2) {
    if (bots && r() < 0.04) return BOT;
    return atom(pick(r, atoms));
  }
  const x = r();
  if (x < 0.18) return not(randomFormula(r, atoms, depth - 1, { iffs, bots }));
  const ops = iffs ? [and, or, imp, imp, iff] : [and, or, imp, imp];
  const op = pick(r, ops);
  return op(randomFormula(r, atoms, depth - 1, { iffs, bots }), randomFormula(r, atoms, depth - 1, { iffs, bots }));
}

export function seq(text) {
  return parseSequent(text);
}
