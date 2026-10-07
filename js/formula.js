// Formulas of propositional logic: construction, parsing and printing.
//
// Formulas are hash-consed: building the same formula twice gives the very
// same frozen object, so equality of formulas is just ===.
//
//   { t: 'atom', name }      { t: 'bot' }          { t: 'not', a }
//   { t: 'and', a, b }       { t: 'or', a, b }     { t: 'imp', a, b }
//   { t: 'iff', a, b }
//
// Every formula also carries a unique numeric id, a canonical key and its size.

const table = new Map();
let nextId = 1;

function intern(key, make) {
  let f = table.get(key);
  if (!f) {
    f = make();
    f.key = key;
    f.id = nextId++;
    Object.freeze(f);
    table.set(key, f);
  }
  return f;
}

export function atom(name) {
  return intern(name, () => ({ t: 'atom', name, size: 1 }));
}
export const BOT = intern('⊥', () => ({ t: 'bot', size: 1 }));
export function not(a) {
  return intern('¬' + a.key, () => ({ t: 'not', a, size: a.size + 1 }));
}
function binary(t, sym) {
  return (a, b) =>
    intern('(' + a.key + sym + b.key + ')', () => ({ t, a, b, size: a.size + b.size + 1 }));
}
export const and = binary('and', '∧');
export const or = binary('or', '∨');
export const imp = binary('imp', '→');
export const iff = binary('iff', '↔');

export const SYMBOL = { and: '∧', or: '∨', imp: '→', iff: '↔' };
export const isBinary = (f) => f.t === 'and' || f.t === 'or' || f.t === 'imp' || f.t === 'iff';

// ---------------------------------------------------------------------------
// Tokeniser

// Longest symbols first, so that "->" wins over "-" and "|-" over "|".
const SYMBOLS = [
  ['<-->', 'iff'], ['<==>', 'iff'], ['-->', 'imp'], ['==>', 'imp'], ['—>', 'imp'], ['–>', 'imp'],
  ['_|_', 'bot'], ['<->', 'iff'], ['<=>', 'iff'],
  ['->', 'imp'], ['=>', 'imp'], ['/\\', 'and'], ['\\/', 'or'], ['&&', 'and'], ['||', 'or'],
  ['|-', 'turnstile'], ['⊢', 'turnstile'], ['⊦', 'turnstile'],
  ['↔', 'iff'], ['⇔', 'iff'], ['≡', 'iff'], ['⟷', 'iff'],
  ['→', 'imp'], ['⇒', 'imp'], ['⊃', 'imp'], ['⟶', 'imp'],
  ['∧', 'and'], ['&', 'and'], ['^', 'and'], ['⋀', 'and'],
  ['∨', 'or'], ['|', 'or'], ['⋁', 'or'],
  ['¬', 'not'], ['~', 'not'], ['!', 'not'], ['-', 'not'], ['−', 'not'], ['￢', 'not'],
  ['⊥', 'bot'], ['(', 'lp'], [')', 'rp'], [',', 'comma'],
];

const WORDS = {
  and: 'and', or: 'or', not: 'not', implies: 'imp', iff: 'iff',
  bot: 'bot', false: 'bot', falsum: 'bot', bottom: 'bot',
};

const UNSUPPORTED_WORDS = new Set(['true', 'top', 'xor']);

const SHOW_TOKEN = {
  and: '∧', or: '∨', imp: '→', iff: '↔', not: '¬', bot: '⊥',
  lp: '(', rp: ')', comma: ',', turnstile: '⊢',
};

export class ParseError extends Error {
  constructor(message, pos, length = 1) {
    super(message);
    this.pos = pos;
    this.length = length;
  }
}

const IDENT = /[\p{L}][\p{L}\p{N}_']*/uy;

export function tokenise(src) {
  const tokens = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (/\s/u.test(ch)) { i++; continue; }
    if (src.startsWith('||-', i)) {
      throw new ParseError('"||-" is ambiguous. Write "|-" for ⊢, or "| ~" for "or not".', i, 3);
    }
    let matched = false;
    for (const [sym, type] of SYMBOLS) {
      if (src.startsWith(sym, i)) {
        tokens.push({ type, text: sym, pos: i });
        i += sym.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;
    IDENT.lastIndex = i;
    const m = IDENT.exec(src);
    if (m) {
      const word = m[0];
      const lower = word.toLowerCase();
      if (word.length > 1 && WORDS[lower]) {
        tokens.push({ type: WORDS[lower], text: word, pos: i });
      } else if (word.length > 1 && UNSUPPORTED_WORDS.has(lower)) {
        throw new ParseError(`"${word}" is not part of the course notation. Use atoms, ⊥, ¬, ∧, ∨, → and ↔.`, i, word.length);
      } else {
        tokens.push({ type: 'atom', text: word, pos: i });
      }
      i += word.length;
      continue;
    }
    if (ch === '⊤') throw new ParseError('⊤ (true) is not part of the course notation.', i);
    if (ch === '[' || ch === '{') throw new ParseError(`Use round brackets ( ) instead of "${ch}".`, i);
    throw new ParseError(`The symbol "${ch}" is not recognised. Use → ∧ ∨ ¬ ⊥ ⊢ or the ASCII forms -> & | ~ _|_ |-.`, i);
  }
  return tokens;
}

// ---------------------------------------------------------------------------
// Parser.  Precedence: ¬ tightest, then ∧, then ∨, then →, then ↔.
// → is right associative; ∧, ∨ and ↔ group to the left.

class Parser {
  constructor(tokens, src) {
    this.tokens = tokens;
    this.src = src;
    this.i = 0;
  }
  peek() { return this.tokens[this.i]; }
  next() { return this.tokens[this.i++]; }
  endPos() { return this.src.length; }

  expectFormula(after) {
    const t = this.peek();
    if (!t) {
      throw new ParseError(after
        ? `Something is missing after "${SHOW_TOKEN[after.type] || after.text}".`
        : 'Type a formula, for example A ∧ B → A.', this.endPos(), 0);
    }
    return t;
  }

  formula() { return this.iffLevel(); }

  iffLevel() {
    let left = this.impLevel();
    while (this.peek() && this.peek().type === 'iff') {
      const op = this.next();
      const right = this.impLevel(op);
      left = iff(left, right);
    }
    return left;
  }

  impLevel(prevOp) {
    const left = this.orLevel(prevOp);
    if (this.peek() && this.peek().type === 'imp') {
      const op = this.next();
      const right = this.impLevel(op);
      return imp(left, right);
    }
    return left;
  }

  orLevel(prevOp) {
    let left = this.andLevel(prevOp);
    while (this.peek() && this.peek().type === 'or') {
      const op = this.next();
      left = or(left, this.andLevel(op));
    }
    return left;
  }

  andLevel(prevOp) {
    let left = this.unary(prevOp);
    while (this.peek() && this.peek().type === 'and') {
      const op = this.next();
      left = and(left, this.unary(op));
    }
    return left;
  }

  unary(prevOp) {
    const t = this.expectFormula(prevOp);
    switch (t.type) {
      case 'not': {
        this.next();
        return not(this.unary(t));
      }
      case 'atom':
        this.next();
        return atom(t.text);
      case 'bot':
        this.next();
        return BOT;
      case 'lp': {
        this.next();
        const inner = this.formula();
        const close = this.peek();
        if (!close || close.type !== 'rp') {
          if (!close) throw new ParseError('A bracket "(" is never closed.', t.pos);
          throw this.unexpected(close);
        }
        this.next();
        return inner;
      }
      case 'rp':
        throw new ParseError(prevOp
          ? `Something is missing after "${SHOW_TOKEN[prevOp.type] || prevOp.text}".`
          : 'There is a ")" without a matching "(".', t.pos);
      case 'and': case 'or': case 'imp': case 'iff':
        throw new ParseError(prevOp
          ? `Two connectives in a row: "${SHOW_TOKEN[prevOp.type]}" is followed by "${SHOW_TOKEN[t.type]}".`
          : `"${SHOW_TOKEN[t.type]}" needs a formula on its left.`, t.pos, t.text.length);
      case 'comma':
        throw new ParseError(prevOp
          ? `Something is missing after "${SHOW_TOKEN[prevOp.type]}".`
          : 'A comma needs a formula before it.', t.pos);
      case 'turnstile':
        throw new ParseError(prevOp
          ? `Something is missing after "${SHOW_TOKEN[prevOp.type]}".`
          : '"⊢" appears where a formula was expected.', t.pos, t.text.length);
      default:
        throw this.unexpected(t);
    }
  }

  unexpected(t) {
    if (t.type === 'atom') {
      if (t.text === 'v' || t.text === 'V') {
        return new ParseError(`A connective is missing before "${t.text}". Did you mean ∨? Type | or "or".`, t.pos, 1);
      }
      return new ParseError(`A connective is missing before "${t.text}".`, t.pos, t.text.length);
    }
    if (t.type === 'rp') return new ParseError('There is a ")" without a matching "(".', t.pos);
    if (t.type === 'lp') return new ParseError('A connective is missing before "(".', t.pos);
    if (t.type === 'not') return new ParseError('A connective is missing before "¬".', t.pos, t.text.length);
    if (t.type === 'bot') return new ParseError('A connective is missing before "⊥".', t.pos, t.text.length);
    return new ParseError(`Unexpected "${SHOW_TOKEN[t.type] || t.text}".`, t.pos, t.text.length);
  }
}

function parseTokens(tokens, src) {
  const p = new Parser(tokens, src);
  const f = p.formula();
  const rest = p.peek();
  if (rest) throw p.unexpected(rest);
  return f;
}

// Parse a single formula.  Throws ParseError.
export function parseFormula(src) {
  const tokens = tokenise(src);
  if (tokens.length === 0) throw new ParseError('Type a formula, for example A ∧ B → A.', 0, 0);
  for (const t of tokens) {
    if (t.type === 'turnstile' && t.text === '|-') {
      throw new ParseError('"|-" stands for ⊢, which is not allowed inside a formula. For "or not", write "| ~".', t.pos, 2);
    }
    if (t.type === 'turnstile') throw new ParseError('"⊢" is not allowed inside a formula.', t.pos, t.text.length);
    if (t.type === 'comma') throw new ParseError('A comma is not allowed inside a formula.', t.pos);
  }
  return parseTokens(tokens, src);
}

// Parse a sequent "P1, P2, ... ⊢ G".  Without ⊢ the whole input is the goal.
// Returns { premises: [formula], goal: formula }.  Throws ParseError.
export function parseSequent(src) {
  const tokens = tokenise(src);
  if (tokens.length === 0) throw new ParseError('Type a sequent, for example A ∧ B ⊢ B ∧ A.', 0, 0);
  const turnstiles = tokens.filter((t) => t.type === 'turnstile');
  if (turnstiles.length > 1) {
    throw new ParseError('Use "⊢" only once: premises on the left, one goal on the right.', turnstiles[1].pos, turnstiles[1].text.length);
  }
  let left = [];
  let right = tokens;
  if (turnstiles.length === 1) {
    const k = tokens.indexOf(turnstiles[0]);
    left = tokens.slice(0, k);
    right = tokens.slice(k + 1);
    if (right.length === 0) {
      throw new ParseError('There is no goal after "⊢".', src.length, 0);
    }
  } else {
    const comma = tokens.find((t) => t.type === 'comma');
    if (comma) throw new ParseError('Use "⊢" (or |-) to separate the premises from the goal.', comma.pos);
  }
  const premises = [];
  if (left.length) {
    let start = 0;
    for (let i = 0; i <= left.length; i++) {
      if (i === left.length || left[i].type === 'comma') {
        const part = left.slice(start, i);
        if (part.length === 0) {
          const pos = i < left.length ? left[i].pos : turnstiles[0].pos;
          throw new ParseError('A premise is missing (two commas in a row, or a comma just before ⊢).', pos);
        }
        premises.push(parseTokens(part, src));
        start = i + 1;
      }
    }
  }
  const commaR = right.find((t) => t.type === 'comma');
  if (commaR) throw new ParseError('Only one goal is allowed after "⊢".', commaR.pos);
  const goal = parseTokens(right, src);
  return { premises, goal };
}

// Non-throwing wrapper for the user interface.
export function tryParseSequent(src) {
  try {
    return { ok: true, ...parseSequent(src) };
  } catch (e) {
    if (e instanceof ParseError) return { ok: false, error: e.message, pos: e.pos, length: e.length };
    throw e;
  }
}

// ---------------------------------------------------------------------------
// Printing.  A binary subformula of a binary formula (or of ¬) is always
// bracketed; there are no outer brackets; binary connectives get spaces.

function printer(sym, atomFn, botText, notText, wrapL = '(', wrapR = ')', space = ' ') {
  const go = (f) => {
    switch (f.t) {
      case 'atom': return atomFn(f.name);
      case 'bot': return botText;
      case 'not': return notText + (isBinary(f.a) ? wrapL + go(f.a) + wrapR : go(f.a));
      default: {
        const w = (x) => (isBinary(x) ? wrapL + go(x) + wrapR : go(x));
        return w(f.a) + space + sym[f.t] + space + w(f.b);
      }
    }
  };
  return go;
}

export const show = printer(SYMBOL, (n) => n, '⊥', '¬');

export const showAscii = printer({ and: '&', or: '|', imp: '->', iff: '<->' }, (n) => n, '_|_', '~');

const latexAtom = (n) => (n.length === 1 ? n : `\\mathit{${n.replace(/_/g, '\\_')}}`);
export const showLatex = printer(
  { and: '\\land', or: '\\lor', imp: '\\to', iff: '\\leftrightarrow' },
  latexAtom, '\\bot', '\\neg ',
);

export function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}

// HTML with atoms in italic and connectives marked up for styling.
export const showHtml = printer(
  {
    and: '<span class="op">∧</span>', or: '<span class="op">∨</span>',
    imp: '<span class="op">→</span>', iff: '<span class="op">↔</span>',
  },
  (n) => `<span class="atom">${escapeHtml(n)}</span>`,
  '<span class="bot">⊥</span>',
  '<span class="op neg">¬</span>',
  '<span class="br">(</span>', '<span class="br">)</span>',
);

// Words for screen readers.
export function speak(f) {
  switch (f.t) {
    case 'atom': return f.name;
    case 'bot': return 'falsum';
    case 'not': return 'not ' + (isBinary(f.a) ? 'open bracket ' + speak(f.a) + ' close bracket' : speak(f.a));
    default: {
      const w = (x) => (isBinary(x) ? 'open bracket ' + speak(x) + ' close bracket' : speak(x));
      const word = { and: 'and', or: 'or', imp: 'implies', iff: 'if and only if' }[f.t];
      return w(f.a) + ' ' + word + ' ' + w(f.b);
    }
  }
}

export function showSequent(premises, goal, fn = show) {
  const turn = fn === showAscii ? '|-' : fn === showLatex ? '\\vdash' : '⊢';
  const left = premises.map(fn).join(', ');
  return (left ? left + ' ' : '') + turn + ' ' + fn(goal);
}

export function showSequentHtml(premises, goal) {
  const left = premises.map(showHtml).join('<span class="comma">,</span> ');
  return (left ? left + ' ' : '') + '<span class="turnstile">⊢</span> ' + showHtml(goal);
}

// ---------------------------------------------------------------------------
// Utilities

export function atomsOf(formulas) {
  const seen = new Set();
  const out = [];
  const walk = (f) => {
    switch (f.t) {
      case 'atom':
        if (!seen.has(f.name)) { seen.add(f.name); out.push(f.name); }
        break;
      case 'bot': break;
      case 'not': walk(f.a); break;
      default: walk(f.a); walk(f.b);
    }
  };
  for (const f of formulas) walk(f);
  return out.sort((x, y) => (x.length - y.length) || (x < y ? -1 : x > y ? 1 : 0));
}

export function connectivesOf(formulas) {
  const seen = new Set();
  const walk = (f) => {
    seen.add(f.t);
    if (f.a) walk(f.a);
    if (f.b) walk(f.b);
  };
  for (const f of formulas) walk(f);
  return seen;
}

export function subformulas(formulas) {
  const seen = new Set();
  const out = [];
  const walk = (f) => {
    if (seen.has(f)) return;
    seen.add(f);
    if (f.a) walk(f.a);
    if (f.b) walk(f.b);
    out.push(f);
  };
  for (const f of formulas) walk(f);
  return out;
}

// The main connective in words, for explanations.
export const CONNECTIVE_NAME = {
  atom: 'an atom', bot: 'falsum', not: '¬', and: '∧', or: '∨', imp: '→', iff: '↔',
};
