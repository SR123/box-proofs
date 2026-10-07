// Exporting a proof: a self-contained TikZ picture and an SVG drawing.

import { show, showLatex, showSequent, escapeHtml, isBinary } from './formula.js';
import { layoutRows, justificationText } from './proof.js';

// ---------------------------------------------------------------------------
// LaTeX (TikZ)

// Rough width of a formula in LaTeX math at 10pt, in cm.
function texWidth(f) {
  const wrap = (x) => (isBinary(x) ? 0.3 + texWidth(x) : texWidth(x));
  switch (f.t) {
    case 'atom': return 0.2 + 0.12 * f.name.length;
    case 'bot': return 0.3;
    case 'not': return 0.25 + wrap(f.a);
    default: return wrap(f.a) + 0.62 + wrap(f.b);
  }
}

function justLatex(text) {
  return text
    .replace(/–/g, '--')
    .replace(/∧/g, '$\\land$\\,')
    .replace(/∨/g, '$\\lor$\\,')
    .replace(/→/g, '$\\to$\\,')
    .replace(/↔/g, '$\\leftrightarrow$\\,')
    .replace(/¬/g, '$\\neg$\\,')
    .replace(/\$\\,\s+/g, '$\\,');
}

const n2 = (x) => (Math.round(x * 100) / 100).toString();

export function proofToTikz(p) {
  const { rows, boxes, nb } = layoutRows(p);
  const rowH = 0.65;
  const indent = 0.5;
  const numX = 0.6;
  const fx0 = numX + 0.4;
  const maxDepth = Math.max(0, ...rows.map((r) => r.depth));
  const widest = Math.max(1, ...rows.map((r) => r.depth * indent + (r.kind === 'gap' ? 0.2 : texWidth(r.line.f))));
  const jx = fx0 + widest + 0.5 + 0.15 * maxDepth;
  const y = (i) => -(i + 1) * rowH;
  const out = [];
  out.push(`% Box proof of ${showSequent(p.premises, p.goal)}`);
  out.push('% Needs \\usepackage{tikz} in the preamble.');
  out.push('\\begin{tikzpicture}[every node/.style={inner sep=0pt, outer sep=0pt}]');
  out.push('  \\definecolor{bpInk}{HTML}{183452}');
  out.push('  \\definecolor{bpblue}{HTML}{2856A6}');
  out.push('  \\definecolor{bpmuted}{HTML}{647080}');
  for (const b of boxes) {
    const x1 = fx0 + (b.depth - 1) * indent - 0.18;
    const x2 = jx - 0.25 - (b.depth - 1) * 0.15;
    // Adjacent boxes (the two cases of ∨ elim) are 0.15 cm apart.
    const top = y(b.startRow) + 0.38;
    const bottom = y(b.endRow) - 0.12;
    out.push(`  \\draw[bpblue, line width=0.5pt, rounded corners=2.5pt] (${n2(x1)},${n2(top)}) rectangle (${n2(x2)},${n2(bottom)});`);
  }
  rows.forEach((r, i) => {
    const fx = fx0 + r.depth * indent;
    if (r.kind === 'gap') {
      out.push(`  \\node[anchor=base west, text=bpmuted] at (${n2(fx)},${n2(y(i))}) {$\\vdots$};`);
      return;
    }
    out.push(`  \\node[anchor=base east, text=bpmuted] at (${n2(numX)},${n2(y(i))}) {\\small ${r.num}};`);
    out.push(`  \\node[anchor=base west, text=bpInk] at (${n2(fx)},${n2(y(i))}) {$${showLatex(r.line.f)}$};`);
    const j = r.line.rule === null ? '?' : justLatex(justificationText(r.line, nb));
    out.push(`  \\node[anchor=base west, text=bpInk] at (${n2(jx)},${n2(y(i))}) {\\small ${j}};`);
  });
  out.push('\\end{tikzpicture}');
  return out.join('\n');
}

// ---------------------------------------------------------------------------
// SVG

let measureCtx = null;
function measure(text, font) {
  try {
    if (!measureCtx && typeof document !== 'undefined') {
      measureCtx = document.createElement('canvas').getContext('2d');
    }
    if (measureCtx) {
      measureCtx.font = font;
      return measureCtx.measureText(text).width;
    }
  } catch (e) {
    // fall through to the estimate
  }
  const size = parseFloat(/(\d+(?:\.\d+)?)px/.exec(font)?.[1] || '18');
  return text.length * size * 0.56;
}

const FONT_FAMILY = "'Inter', 'Segoe UI', 'Helvetica Neue', Arial, sans-serif";

function svgFormula(f) {
  // Atoms in italic, everything else upright.
  const parts = [];
  const go = (g) => {
    switch (g.t) {
      case 'atom': parts.push(`<tspan font-style="italic">${escapeHtml(g.name)}</tspan>`); break;
      case 'bot': parts.push('⊥'); break;
      case 'not':
        parts.push('¬');
        if (isBinary(g.a)) { parts.push('('); go(g.a); parts.push(')'); } else go(g.a);
        break;
      default: {
        const sym = { and: '∧', or: '∨', imp: '→', iff: '↔' }[g.t];
        const w = (x) => { if (isBinary(x)) { parts.push('('); go(x); parts.push(')'); } else go(x); };
        w(g.a);
        parts.push(` ${sym} `);
        w(g.b);
      }
    }
  };
  go(f);
  return parts.join('');
}

export function proofToSvg(p, { dark = false } = {}) {
  const { rows, boxes, nb } = layoutRows(p);
  const size = 18;
  const font = `${size}px ${FONT_FAMILY}`;
  const smallFont = `${size * 0.85}px ${FONT_FAMILY}`;
  const colours = dark
    ? { bg: '#0f1b2b', ink: '#e4ecf7', blue: '#8fb3f0', muted: '#9aa7b8', teal: '#4fc3cf' }
    : { bg: '#ffffff', ink: '#183452', blue: '#2856A6', muted: '#647080', teal: '#087F8C' };
  const rowH = 36;
  const pad = 20;
  const numW = Math.max(28, measure(String(nb.count), font) + 12);
  const indent = 22;
  const fx0 = pad + numW + 14;
  const maxDepth = Math.max(0, ...rows.map((r) => r.depth));
  const widths = rows.map((r) => (r.kind === 'gap' ? 10 : measure(show(r.line.f), font) * 1.04));
  const widest = Math.max(60, ...rows.map((r, i) => r.depth * indent + widths[i]));
  const jx = fx0 + widest + 24 + 8 * maxDepth;
  const justW = Math.max(60, ...rows.map((r) => (r.kind === 'line' && r.line.rule ? measure(justificationText(r.line, nb), smallFont) : 0)));
  const W = Math.ceil(jx + justW + pad);
  const H = Math.ceil(pad * 2 + rows.length * rowH);
  const base = (i) => pad + i * rowH + rowH * 0.66;
  const out = [];
  out.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" font-family="${FONT_FAMILY.replace(/"/g, "'")}" font-size="${size}">`);
  out.push(`  <title>${escapeHtml('Box proof of ' + showSequent(p.premises, p.goal))}</title>`);
  out.push(`  <rect width="${W}" height="${H}" fill="${colours.bg}"/>`);
  for (const b of boxes) {
    const x1 = fx0 + (b.depth - 1) * indent - 8;
    const x2 = jx - 12 - (b.depth - 1) * 6;
    const top = pad + b.startRow * rowH + 3;
    const bottom = pad + (b.endRow + 1) * rowH - 3;
    out.push(`  <rect x="${n2(x1)}" y="${n2(top)}" width="${n2(x2 - x1)}" height="${n2(bottom - top)}" rx="7" fill="none" stroke="${colours.blue}" stroke-width="1.5"/>`);
  }
  rows.forEach((r, i) => {
    const fx = fx0 + r.depth * indent;
    if (r.kind === 'gap') {
      out.push(`  <text x="${n2(fx + 2)}" y="${n2(base(i))}" fill="${colours.muted}">⋮</text>`);
      return;
    }
    out.push(`  <text x="${n2(pad + numW)}" y="${n2(base(i))}" fill="${colours.muted}" text-anchor="end" font-size="${n2(size * 0.85)}">${r.num}</text>`);
    out.push(`  <text x="${n2(fx)}" y="${n2(base(i))}" fill="${colours.ink}">${svgFormula(r.line.f)}</text>`);
    const j = r.line.rule === null ? '' : escapeHtml(justificationText(r.line, nb));
    if (j) out.push(`  <text x="${n2(jx)}" y="${n2(base(i))}" fill="${colours.ink}" font-size="${n2(size * 0.85)}">${j}</text>`);
  });
  out.push('</svg>');
  return out.join('\n');
}
