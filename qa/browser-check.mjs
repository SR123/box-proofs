// Browser check with Playwright (Chromium).
//
//   node qa/browser-check.mjs
//
// Serves the app with "python3 -m http.server", drives the user interface,
// fails on console errors, and saves screenshots to qa/.  Playwright is not
// a dependency of the app: the script uses a globally installed copy (or set
// PLAYWRIGHT_MODULE to the path of playwright's index.mjs).

import { spawn, execSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { dirname, join } from 'node:path';
import { existsSync, readdirSync, unlinkSync } from 'node:fs';
import assert from 'node:assert/strict';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const PORT = 8000 + Math.floor(Math.random() * 900) + 50;
const BASE = `http://127.0.0.1:${PORT}/`;

async function loadPlaywright() {
  const candidates = [];
  if (process.env.PLAYWRIGHT_MODULE) candidates.push(process.env.PLAYWRIGHT_MODULE);
  try { candidates.push(join(execSync('npm root -g').toString().trim(), 'playwright', 'index.mjs')); } catch (e) { /* no npm */ }
  for (const c of candidates) {
    if (existsSync(c)) return import(pathToFileURL(c).href);
  }
  return import('playwright');
}

const { chromium } = await loadPlaywright();

// Start from a clean set of screenshots.
for (const f of readdirSync(here)) if (f.endsWith('.png')) unlinkSync(join(here, f));

const server = spawn('python3', ['-m', 'http.server', String(PORT), '--bind', '127.0.0.1'], { cwd: root, stdio: 'ignore' });
const stop = () => { try { server.kill(); } catch (e) { /* already gone */ } };
process.on('exit', stop);

async function waitForServer() {
  for (let i = 0; i < 50; i++) {
    try {
      const r = await fetch(BASE + 'index.html');
      if (r.ok) return;
    } catch (e) { /* not yet */ }
    await new Promise((res) => setTimeout(res, 100));
  }
  throw new Error('the static server did not start');
}

let browser;
try {
  browser = await chromium.launch();
} catch (e) {
  browser = await chromium.launch({ executablePath: '/opt/pw-browsers/chromium' });
}

const results = [];
const problems = [];
function step(name) { results.push(name); console.log('✓', name); }

async function newPage({ width = 1280, height = 800, scheme = 'light' } = {}) {
  const context = await browser.newContext({ viewport: { width, height }, colorScheme: scheme, reducedMotion: 'reduce' });
  try { await context.grantPermissions(['clipboard-read', 'clipboard-write'], { origin: BASE.replace(/\/$/, '') }); } catch (e) { /* not supported */ }
  const page = await context.newPage();
  page.on('console', (m) => { if (m.type() === 'error') problems.push(`console error: ${m.text()}`); });
  page.on('pageerror', (e) => problems.push(`page error: ${e.message}`));
  page.on('requestfailed', (r) => problems.push(`request failed: ${r.url()}`));
  page.on('request', (r) => { if (!r.url().startsWith(BASE) && !r.url().startsWith('data:') && !r.url().startsWith('blob:') && r.url() !== 'about:blank') problems.push(`external request: ${r.url()}`); });
  return page;
}

const text = (page, sel) => page.$eval(sel, (el) => el.textContent.replace(/\s+/g, ' ').trim());
const shot = (page, name) => page.screenshot({ path: join(here, name) });
const complete = async (page) => !(await page.$eval('#complete-banner', (el) => el.hidden));
const openGoalCount = (page) => page.$$eval('#proof-scroll .row.goal', (els) => els.length);
const lineTexts = (page) => page.$$eval('#proof-scroll .row[role="option"]', (rs) => rs.map((r) => [...r.children].map((c) => c.textContent.trim()).join(' ').replace(/\s+/g, ' ')));

async function noHorizontalScroll(page, label) {
  const { sw, iw } = await page.evaluate(() => ({ sw: document.documentElement.scrollWidth, iw: window.innerWidth }));
  assert.ok(sw <= iw + 1, `${label}: the page scrolls sideways (${sw} > ${iw})`);
}

async function inViewport(page, sel, label) {
  const box = await page.$eval(sel, (el) => { const r = el.getBoundingClientRect(); return { top: r.top, bottom: r.bottom, left: r.left, right: r.right, h: window.innerHeight, w: window.innerWidth }; });
  assert.ok(box.top >= 0 && box.bottom <= box.h && box.left >= 0 && box.right <= box.w, `${label}: ${sel} is not inside the window (${JSON.stringify(box)})`);
}

// Press Next in Show me until the proof is complete.
async function playToEnd(page, prefix = '') {
  for (let i = 0; i < 40 && !(await complete(page)); i++) await page.click(`${prefix}[data-show="next"]`);
}

try {
  await waitForServer();

  // 1. Load the app, no console errors, build A ∧ B ⊢ B ∧ A by clicking.
  {
    const page = await newPage();
    await page.goto(BASE);
    await page.waitForSelector('#proof-scroll .row');
    await page.click('[data-ex="and-1"]');
    assert.equal(await text(page, '#sequent'), 'A ∧ B ⊢ B ∧ A');
    await page.click('[data-rule="andI"]');
    assert.equal(await openGoalCount(page), 2);
    // The first new goal (B) is selected; use line 1 with ∧ elim.
    await page.click('#proof-scroll .row[data-kind="line"] >> nth=0');
    await page.click('#rule-panel [data-rule="andE"]');
    const choices = await page.$$eval('#chooser [data-choice]', (bs) => bs.map((b) => b.textContent.replace(/\s+/g, ' ').trim()));
    assert.deepEqual(choices, ['Line 1 gives Acloses the goal on line 3', 'Line 1 gives Bcloses this goal', 'Cancel']);
    await page.click('#chooser button:has-text("Line 1 gives B")');
    assert.equal(await openGoalCount(page), 1);
    await page.click('#proof-scroll .row[data-kind="line"] >> nth=0');
    await page.click('#rule-panel [data-rule="andE"]'); // only "A" is left, so it applies at once
    assert.ok(await complete(page), 'A ∧ B ⊢ B ∧ A should be complete');
    assert.deepEqual(await lineTexts(page), ['1 A ∧ B premise', '2 B ∧ elim 1', '3 A ∧ elim 1', '4 B ∧ A ∧ intro 2,3']);
    // Hovering a justification shades the lines it uses.
    await page.hover('#proof-scroll .row[data-kind="line"] >> nth=3 >> .jtext');
    const shaded = await page.$$eval('#proof-scroll .row.hl', (rs) => rs.map((r) => r.querySelector('.num').textContent));
    assert.deepEqual(shaded, ['2', '3']);
    await shot(page, 'desktop-light-and-complete.png');
    // Undo with the keyboard, then redo.
    await page.mouse.click(5, 790);
    await page.keyboard.press('Control+z');
    assert.equal(await complete(page), false);
    await page.keyboard.press('Control+Shift+z');
    assert.ok(await complete(page));
    step('built A ∧ B ⊢ B ∧ A by clicking; the chooser says which goal each option closes; hover shading, undo and redo work');

    // Your own sequent: palette, live preview, friendly errors.
    await page.fill('#own-input', 'A');
    await page.click('.palette [data-sym="∧"]');
    assert.match(await text(page, '#own-error'), /missing after "∧"/);
    await page.fill('#own-input', 'A v B |- B v A');
    assert.match(await text(page, '#own-error'), /Did you mean ∨\?/);
    await page.fill('#own-input', 'A -> B, ~B |- ~A');
    assert.equal(await text(page, '#own-preview'), 'Reads as A → B, ¬B ⊢ ¬A');
    await page.click('#own-start');
    assert.equal(await text(page, '#sequent'), 'A → B, ¬B ⊢ ¬A');
    assert.equal(await text(page, '#problem-title'), 'Your own sequent');
    assert.equal(await page.$eval('#game-select', (s) => s.value), 'not');
    await page.click('#solve-btn');
    assert.ok(await complete(page));
    step('your own sequent: palette, live preview, parse errors (including "A v B"), and the prover finishes it');
    await page.context().close();
  }

  // 2. Greyed-out rules explain themselves next to the button, also at 1280×720.
  {
    const page = await newPage({ width: 1280, height: 720 });
    await page.goto(`${BASE}?ex=imp-1`);
    await page.click('[data-rule="impI"]');
    await page.click('#rule-panel [data-rule="andI"]', { force: true }); // aria-disabled buttons still respond
    assert.equal(await page.$eval('#tip', (t) => t.hidden), false);
    assert.match(await text(page, '#tip'), /not a conjunction/);
    await inViewport(page, '#tip', 'rule reason at 1280×720');
    await shot(page, 'desktop-1280x720-rule-reason.png');
    // ¬ elim in ¬¬A ⊢ A points to contra (classical), not to a dead end.
    await page.goto(`${BASE}?ex=cl-1`);
    await page.click('#rule-panel [data-rule="notE"]', { force: true });
    assert.match(await text(page, '#tip'), /contra \(classical\)/);
    assert.doesNotMatch(await text(page, '#tip'), /use contra first/);
    // A line in a closed box: the reason appears next to the line.
    await page.goto(`${BASE}?ex=or-4`);
    await page.click('[data-rule="orE"]');
    await page.click('[data-rule="impE"]');
    await page.click('#chooser button >> nth=0');
    // The first case is closed now; the second case's goal cannot use line 4.
    await page.click('#proof-scroll .row[data-kind="line"] >> nth=3');
    assert.match(await text(page, '#tip'), /closed|after the goal/);
    step('greyed-out rules and out-of-bounds lines explain themselves in a tip next to what was clicked');
    await page.context().close();
  }

  // 3. Guided mode and Show me on ⊢ A → (B → A) and A ∨ B ⊢ B ∨ A.
  for (const [ex, game] of [['imp-2', 'imp'], ['or-2', 'or']]) {
    const page = await newPage();
    await page.goto(`${BASE}?ex=${ex}&mode=guided`);
    await page.waitForSelector('.move-list');
    assert.equal(await page.$eval('#game-select', (s) => s.value), game);
    const first = await page.$$eval('.move', (ms) => ms.map((m) => `${m.querySelector('.badge').textContent} ${m.querySelector('.move-title').textContent.replace(/\s+/g, ' ').trim()}`));
    if (ex === 'imp-2') assert.deepEqual(first, ['✓ 1→ introsuggested']);
    if (ex === 'or-2') {
      assert.ok(first.some((t) => t.startsWith('✗') && t.includes('∨ intro (left): B')), first.join(' | '));
      assert.ok(first.some((t) => t.startsWith('✓') && t.includes('∨ elim on line 1')), first.join(' | '));
      // In guided mode the rule buttons are marked ✓ or ✗ as well.
      assert.match(await text(page, '#rule-panel [data-rule="orE"]'), /✓/);
      assert.match(await text(page, '#rule-panel [data-rule="orIL"]'), /✗/);
    }
    await shot(page, `desktop-light-guided-${ex}.png`);
    // Follow the ✓ moves until done.
    for (let i = 0; i < 12 && !(await complete(page)); i++) {
      await page.click('.move.ok [data-apply] >> nth=0');
    }
    assert.ok(await complete(page), `${ex}: guided mode should reach a complete proof`);
    step(`guided mode completes ${ex}`);

    // Show me from the start.
    await page.click('#restart-btn');
    await page.click('#show-btn');
    await page.waitForSelector('.show-controls');
    const count = await text(page, '.step-count');
    const n = Number(/of (\d+)/.exec(count)[1]);
    assert.ok(n >= 2, count);
    assert.ok(await page.$eval('#next-btn', (b) => b.disabled), 'Moves is disabled during Show me');
    await page.click('[data-show="next"]');
    if (ex === 'or-2') await shot(page, 'desktop-light-showme-or-2.png');
    await playToEnd(page, '.show-controls ');
    assert.equal(await text(page, '.step-count'), `Step ${n} of ${n}`);
    await page.click('[data-show="prev"]');
    assert.equal(await complete(page), false);
    await page.click('[data-show="play"]');
    await page.waitForFunction(() => !document.querySelector('#complete-banner').hidden, null, { timeout: 10000 });
    step(`Show me builds ${ex} step by step (Next, Previous, Play)`);
    await page.context().close();
  }

  // 4. Shared URLs (Unicode and ASCII), game and mode parameters, embed mode.
  {
    const page = await newPage();
    await page.goto(`${BASE}?s=A%E2%88%A7B%20%E2%8A%A2%20B%E2%88%A7A`);
    assert.equal(await text(page, '#sequent'), 'A ∧ B ⊢ B ∧ A');
    assert.equal(await text(page, '#problem-title'), 'Swap a conjunction');
    await page.goto(`${BASE}?s=A%26B%7C-B%26A&game=full`);
    assert.equal(await text(page, '#sequent'), 'A ∧ B ⊢ B ∧ A');
    assert.equal(await page.$eval('#game-select', (s) => s.value), 'full');
    await page.goto(`${BASE}?s=A&B|-B&A&game=and`); // unencoded & still works
    assert.equal(await text(page, '#sequent'), 'A ∧ B ⊢ B ∧ A');
    await page.goto(`${BASE}?s=p%20-%3E%20q%2C%20~q%20%7C-%20~p&mode=guided`);
    assert.equal(await text(page, '#sequent'), 'p → q, ¬q ⊢ ¬p');
    assert.ok(await page.$eval('#guided-toggle', (c) => c.checked));
    assert.equal(await page.$eval('#game-select', (s) => s.value), 'not');
    // A typed invalid sequent shows its counterexample at once.
    await page.goto(`${BASE}?s=A%20%E2%86%92%20B%20%E2%8A%A2%20B%20%E2%86%92%20A`);
    assert.match(await text(page, '#guide-body'), /With A = 0, B = 1, every premise is true but the goal B → A is false/);
    assert.match(await text(page, '#problem-status'), /Not valid/);
    await shot(page, 'desktop-light-counterexample.png');
    // Copy link gives a short URL that loads the same problem.
    await page.goto(`${BASE}?ex=both-3`);
    await page.click('#export-menu summary');
    await page.click('#copy-link');
    const link = await page.evaluate(() => navigator.clipboard.readText());
    assert.match(link, /\?ex=both-3$/);
    await page.goto(link);
    assert.equal(await text(page, '#sequent'), 'A → (B → C) ⊢ (A ∧ B) → C');
    await page.selectOption('#game-select', 'full');
    await page.click('#export-menu summary');
    await page.click('#copy-link');
    assert.match(await page.evaluate(() => navigator.clipboard.readText()), /\?ex=both-3&game=full$/);
    // An unknown exercise id says so.
    await page.goto(`${BASE}?ex=nope`);
    assert.match(await text(page, '#toast'), /There is no exercise “nope”/);
    assert.match(page.url(), /\?ex=and-1/);
    // ?solve=0 hides Solve and Show me.
    await page.goto(`${BASE}?ex=imp-1&solve=0`);
    assert.ok(await page.$eval('#solve-btn', (b) => b.hidden));
    assert.ok(await page.$eval('#show-btn', (b) => b.hidden));
    // Embed mode hides the header and the library.
    await page.goto(`${BASE}?ex=or-4&embed=1`);
    assert.equal(await page.$eval('.topbar', (el) => getComputedStyle(el).display), 'none');
    assert.equal(await page.$eval('.sidebar', (el) => getComputedStyle(el).display), 'none');
    step('shared URLs (Unicode, ASCII, unencoded &), game, mode, solve=0 and embed parameters work; Copy link is short and round-trips; an unknown id is reported');
    await page.context().close();
  }

  // 5. Embedded in an iframe of the suggested height: the guide is in view.
  for (const width of [1000, 720]) {
    const page = await newPage({ width, height: 900 });
    await page.setContent(`<!doctype html><html><body style="margin:0;padding:16px;background:#eee"><iframe src="${BASE}?ex=or-4&embed=1" title="Box proof" style="border:0;width:100%;height:760px;background:#fff"></iframe></body></html>`);
    const frame = page.frames().find((f) => f.url().startsWith(BASE));
    await frame.waitForSelector('#proof-scroll .row');
    const hint = await frame.$eval('#hint-btn', (b) => b.getBoundingClientRect().bottom);
    assert.ok(hint < 760, `embed ${width}: Hint at ${hint}px, below the 760 px frame`);
    const link = await frame.$eval('#open-full', (a) => ({ bottom: a.getBoundingClientRect().bottom, href: a.href }));
    assert.ok(link.bottom < 760 && !/embed=1/.test(link.href), 'embed: "Open in the full app" is visible and links to the full app');
    await shot(page, `embed-iframe-${width}.png`);
    await page.context().close();
  }
  step('embedded at 760 px height (1000 and 720 wide): the guide and "Open in the full app" are in view');

  // 6. "Can you prove it?": the verdict waits until the student asks.
  {
    const page = await newPage();
    await page.goto(`${BASE}?ex=imp-7`);
    assert.doesNotMatch(await text(page, '#problem-status'), /Not valid/);
    assert.match(await text(page, '#guide-body'), /Can you prove it\?/);
    assert.equal(await page.$$eval('#proof-scroll .row.goal.dead', (r) => r.length), 0);
    await page.click('[data-rule="impI"]');
    await page.click('[data-rule="impI"]');
    assert.equal(await page.$$eval('#proof-scroll .row.goal.dead', (r) => r.length), 0, 'no dead-end chip yet');
    await shot(page, 'desktop-light-can-you-prove-it.png');
    // Try a wrong row first, then the right one.
    await page.click('[data-action="check-row"]');
    assert.match(await text(page, '#guide-body'), /not a counterexample/);
    await page.click('[data-atom="C"]');
    await page.click('[data-action="check-row"]');
    assert.match(await text(page, '#guide-body'), /✓ Right/);
    assert.match(await text(page, '#problem-status'), /Not valid/);
    assert.ok(await page.$$eval('#proof-scroll .row.goal.dead', (r) => r.length) > 0);
    // Hint reveals it too.
    await page.goto(`${BASE}?ex=imp-7`);
    await page.click('#hint-btn');
    assert.match(await text(page, '#guide-body'), /Hint 1 of 2/);
    await page.click('#hint-btn');
    assert.match(await text(page, '#guide-body'), /Not valid, so there is no proof/);
    step('"Can you prove it?" keeps the verdict back; a correct truth-table row or Hint reveals it');
    await page.context().close();
  }

  // 7. Needs contra (classical): a clear message and a button to switch.
  {
    const page = await newPage();
    await page.goto(`${BASE}?s=~~A%20%7C-%20A&game=not`);
    assert.match(await text(page, '#problem-status'), /Needs contra \(classical\)/);
    await page.click('#solve-btn');
    const body = await text(page, '#guide-body');
    assert.match(body, /These rules are not enough/);
    assert.doesNotMatch(body, /Undo/);
    await page.click('[data-action="full"]');
    assert.equal(await page.$eval('#game-select', (s) => s.value), 'full');
    await page.click('#solve-btn');
    assert.ok(await complete(page));
    step('a sequent that needs contra (classical) says so, never suggests Undo at the start, and offers Full rules');
    await page.context().close();
  }

  // 8. Export and the proof checker dialog.
  {
    const page = await newPage();
    await page.goto(`${BASE}?ex=imp-2`);
    // An unfinished proof is not filled in, and "Use the current proof" says it is not finished.
    await page.click('#check-btn');
    assert.equal(await page.$eval('#check-input', (t) => t.value), '');
    await page.click('#check-current');
    assert.match(await text(page, '#check-result'), /still an open goal, so the proof is not finished/);
    await page.keyboard.press('Escape');
    await page.click('#solve-btn');
    assert.ok(await complete(page));
    assert.match(await text(page, '#guide-body'), /Keep this proof/);
    await page.click('#export-menu summary');
    await page.click('#copy-text');
    const t = await page.evaluate(() => navigator.clipboard.readText());
    assert.match(t, /│ │ A +line 1/);
    await page.click('#export-menu summary');
    await page.click('#copy-latex');
    const tex = await page.evaluate(() => navigator.clipboard.readText());
    assert.match(tex, /\\begin\{tikzpicture\}/);
    assert.match(tex, /bpInk/);
    await page.click('#export-menu summary');
    const [download] = await Promise.all([page.waitForEvent('download'), page.click('#download-svg')]);
    assert.equal(download.suggestedFilename(), 'imp-2.svg');
    // Check a proof: the "spot the bug" proof is rejected.
    await page.click('#export-menu summary');
    await page.click('#check-menu');
    await page.fill('#check-input', '⊢ A\n1 | A        assumption\n2 A → A      → intro 1–1\n3 A          line 1');
    await page.click('#check-run');
    assert.match(await text(page, '#check-result'), /out of bounds/);
    await shot(page, 'desktop-light-check-dialog.png');
    await page.fill('#check-input', t);
    await page.click('#check-run');
    assert.match(await text(page, '#check-result'), /Correct/);
    // A correct proof that needs more rules than the exercise allows.
    await page.fill('#check-input', '1 | A            assumption\n2 | | B          assumption\n3 | | | ¬A       assumption\n4 | | | ⊥        ¬ elim 1,3\n5 | | A          contra (classical) 3–4\n6 | B → A        → intro 2–5\n7 A → (B → A)    → intro 1–6');
    await page.click('#check-run');
    assert.match(await text(page, '#check-result'), /not in the Implication game/);
    await page.click('#check-open');
    assert.equal(await page.$eval('#game-select', (s) => s.value), 'full');
    assert.match(await text(page, '#complete-banner'), /not marked as solved/);
    step('Copy as text, Copy LaTeX, Download SVG and Check a proof work; unfinished and over-powered proofs are reported');
    await page.context().close();
  }
} catch (e) {
  problems.push(`failed: ${e.message}`);
}

// 9. Keyboard operation.
try {
  const page = await newPage();
  await page.goto(`${BASE}?ex=not-1`);
  await page.focus('#proof-scroll .row[tabindex="0"]');
  assert.equal(await page.evaluate(() => document.activeElement.dataset.kind), 'goal');
  await page.keyboard.press('Enter');
  await page.focus('[data-rule="notI"]');
  await page.keyboard.press('Enter');
  assert.equal(await openGoalCount(page), 1);
  // Select the premise and the new assumption with the keyboard, then ¬ elim.
  await page.focus('#proof-scroll .row[tabindex="0"]');
  await page.keyboard.press('Home');
  await page.keyboard.press('Space');
  await page.keyboard.press('ArrowDown');
  await page.keyboard.press('Space');
  const selected = await page.$$eval('#proof-scroll .row.sel', (rs) => rs.map((r) => r.querySelector('.num').textContent));
  assert.deepEqual(selected, ['1', '2']);
  await page.focus('#rule-panel [data-rule="notE"]');
  await page.keyboard.press('Enter');
  assert.ok(await complete(page));
  await page.keyboard.press('Control+z');
  assert.equal(await complete(page), false);
  // Shortcuts: M lists the moves, 1 applies the first.
  await page.focus('body');
  await page.keyboard.press('m');
  await page.waitForSelector('.move-list');
  await page.keyboard.press('1');
  assert.ok(await complete(page));
  // Show me: ← and → work while a proof line has the focus; Redo continues Show me.
  await page.goto(`${BASE}?ex=imp-1`);
  await page.click('#proof-scroll .row[data-kind="line"] >> nth=0');
  await page.keyboard.press('s');
  await page.keyboard.press('ArrowRight');
  assert.match(await text(page, '.step-count'), /Step 1 of/);
  await page.keyboard.press('ArrowRight');
  await page.keyboard.press('ArrowLeft');
  assert.match(await text(page, '.step-count'), /Step 1 of/);
  await page.keyboard.press('Control+Shift+z');
  assert.match(await text(page, '.step-count'), /Step 2 of/, 'Redo is the next step of Show me');
  // ? opens the help.
  await page.keyboard.press('?');
  assert.ok(await page.$eval('#help-dialog', (d) => d.open));
  await shot(page, 'desktop-light-help.png');
  await page.keyboard.press('Escape');
  step('keyboard: select goal and lines, apply rules, undo, M and 1, ← → in Show me (also from a proof line), redo in Show me, ? for help');
  await page.context().close();
} catch (e) {
  problems.push(`keyboard: ${e.message}`);
}

// 10. Layout at classroom sizes, and Present.
try {
  // 1024×768: the guide is beside the proof, not below the fold.
  let page = await newPage({ width: 1024, height: 768 });
  await page.goto(`${BASE}?ex=or-2&mode=guided`);
  await page.waitForSelector('.move-list');
  await inViewport(page, '#hint-btn', 'guide at 1024×768');
  await inViewport(page, '.move >> nth=0', 'first move at 1024×768');
  await shot(page, 'desktop-1024x768-guided.png');
  await page.context().close();
  // Present at 1280×720: no sidebar, a larger proof, the guide beside it.
  page = await newPage({ width: 1280, height: 720 });
  await page.goto(`${BASE}?ex=imp-1`);
  const before = await page.$eval('#proof-scroll .proof', (el) => parseFloat(getComputedStyle(el).fontSize));
  await page.keyboard.press('p');
  assert.ok(await page.$eval('html', (h) => h.classList.contains('present')));
  assert.equal(await page.$eval('#sidebar', (el) => el.getBoundingClientRect().right <= 0), true, 'the sidebar is out of the way');
  const after = await page.$eval('#proof-scroll .proof', (el) => parseFloat(getComputedStyle(el).fontSize));
  assert.ok(after > before * 1.2, `Present makes the proof larger (${before} → ${after})`);
  await page.click('#solve-btn');
  await inViewport(page, '#proof-scroll .row[data-kind="line"]:last-child', 'last line in Present at 1280×720');
  await inViewport(page, '#hint-btn', 'guide in Present at 1280×720');
  await shot(page, 'present-1280x720-solved.png');
  await page.click('#drawer-btn');
  await page.waitForTimeout(300);
  await inViewport(page, '#drawer-close', 'drawer close button');
  await page.click('#drawer-close');
  await page.reload();
  assert.ok(await page.$eval('html', (h) => h.classList.contains('present')), 'Present is remembered');
  await page.keyboard.press('p');
  await page.context().close();
  step('layout: guide in view at 1024×768; Present (P) at 1280×720 shows the whole proof and the guide, and is remembered');
} catch (e) {
  problems.push(`layout: ${e.message}`);
}

// 10b. The start page: a plain address always opens the first exercise with an
// empty proof; the title link goes back there; "Start afresh" also clears ✓ marks.
try {
  const page = await newPage();
  const firstTitle = 'Swap a conjunction';
  await page.goto(`${BASE}?ex=imp-3`);
  await page.waitForSelector('#proof-scroll .row');
  await page.click('#solve-btn');
  assert.ok(await complete(page), 'imp-3 solved');
  assert.equal(await text(page, '[data-ex="imp-3"] .ex-done'), '✓');
  await page.goto(BASE);
  await page.waitForSelector('#proof-scroll .row');
  assert.equal(await text(page, '#problem-title'), firstTitle, 'a plain address opens the first exercise');
  assert.equal(await openGoalCount(page), 1, 'with an empty proof');
  assert.equal(await text(page, '[data-ex="imp-3"] .ex-done'), '✓', 'ticks are kept on a plain reload');
  await page.click('[data-ex="and-3"]');           // a different exercise in the open group
  assert.notEqual(await text(page, '#problem-title'), firstTitle);
  await page.click('#solve-btn');
  await page.click('#home-link');
  assert.equal(await text(page, '#problem-title'), firstTitle, 'the title link opens the start page');
  assert.equal(page.url(), BASE);
  assert.equal(await openGoalCount(page), 1);
  await page.click('#fresh-btn');
  assert.equal(await text(page, '#fresh-btn'), 'Click again to start afresh');
  await page.click('#fresh-btn');
  assert.equal(page.url(), BASE);
  assert.equal(await text(page, '#problem-title'), firstTitle);
  assert.equal(await text(page, '[data-ex="imp-3"] .ex-done'), '', 'ticks are cleared');
  assert.equal(await page.$$eval('.ex-done', (els) => els.filter((e) => e.textContent.trim()).length), 0);
  await page.goto(`${BASE}?ex=and-3`);
  await page.click('#solve-btn');
  await page.goto(`${BASE}?fresh=1`);
  await page.waitForSelector('#proof-scroll .row');
  assert.equal(page.url(), BASE, '?fresh=1 is removed from the address');
  assert.equal(await text(page, '#problem-title'), firstTitle);
  assert.equal(await page.$$eval('.ex-done', (els) => els.filter((e) => e.textContent.trim()).length), 0, '?fresh=1 clears the ticks');
  await shot(page, 'desktop-light-start-page.png');
  await page.context().close();
  step('a plain address and the title link open the first exercise afresh; Start afresh (two clicks) and ?fresh=1 clear the ✓ marks');
} catch (e) {
  problems.push(`start page: ${e.message}`);
}

// 11. Screenshots at 1280×800 and 390×844, light and dark, and phone checks.
try {
  for (const scheme of ['light', 'dark']) {
    const page = await newPage({ scheme });
    await page.goto(`${BASE}?ex=and-1`);
    await shot(page, `desktop-${scheme}-start.png`);
    await page.goto(`${BASE}?ex=cl-4&mode=guided`);
    await page.waitForSelector('.move-list');
    await shot(page, `desktop-${scheme}-guided-classical.png`);
    await page.click('#solve-btn');
    await shot(page, `desktop-${scheme}-solved-classical.png`);
    await page.goto(`${BASE}?ex=or-5`);
    await page.click('#show-btn');
    for (let i = 0; i < 4; i++) await page.click('.show-controls [data-show="next"]');
    await shot(page, `desktop-${scheme}-showme.png`);
    await page.goto(`${BASE}?ex=imp-3`);
    await page.click('[data-rule="impI"]');
    await page.click('[data-rule="impI"]');
    await shot(page, `desktop-${scheme}-imp-3-two-boxes.png`);
    await page.context().close();

    const phone = await newPage({ width: 390, height: 844, scheme });
    await phone.goto(`${BASE}?ex=or-4`);
    await phone.waitForSelector('#proof-scroll .row');
    await noHorizontalScroll(phone, `phone ${scheme} start`);
    await inViewport(phone, '#tray', `phone ${scheme} tray`);
    await shot(phone, `phone-${scheme}-start.png`);
    // Show me from the tray: the controls stay at the bottom, the proof in view.
    await phone.click('#show-btn');
    for (let i = 0; i < 2; i++) await phone.click('#tray [data-show="next"]');
    await noHorizontalScroll(phone, `phone ${scheme} show me`);
    await inViewport(phone, '#proof-scroll .row.goal.cur', `phone ${scheme} current goal during Show me`);
    await shot(phone, `phone-${scheme}-showme.png`);
    // A rule from the tray.
    await phone.goto(`${BASE}?ex=imp-2`);
    await phone.click('#tray [data-rule="impI"]');
    assert.equal(await openGoalCount(phone), 1);
    // A deep proof: the justifications go under the formulas instead of being cut off.
    await phone.goto(`${BASE}?ex=imp-5`);
    await phone.click('#solve-btn');
    await noHorizontalScroll(phone, `phone ${scheme} solved imp-5`);
    const fits = await phone.$eval('#proof-scroll', (el) => el.scrollWidth <= el.clientWidth + 1);
    assert.ok(fits, 'imp-5 fits the phone width');
    await phone.evaluate(() => document.querySelector('#proof-panel').scrollIntoView());
    await shot(phone, `phone-${scheme}-solved-imp-5.png`);
    await phone.goto(`${BASE}?ex=cl-4`);
    await phone.click('#solve-btn');
    await phone.evaluate(() => document.querySelector('#proof-panel').scrollIntoView());
    await shot(phone, `phone-${scheme}-solved-classical.png`);
    // The More menu and the drawer.
    await phone.click('#more-btn');
    assert.ok(await phone.$eval('#game-select', (s) => s.getBoundingClientRect().height > 0));
    await phone.click('#more-btn');
    await phone.click('#drawer-btn');
    await phone.waitForTimeout(300);
    await inViewport(phone, '#drawer-close', `phone ${scheme} drawer close`);
    await shot(phone, `phone-${scheme}-exercises.png`);
    await phone.context().close();
  }
  step('screenshots saved at 1280×800 and 390×844 in light and dark; on the phone: no sideways scrolling, the tray works, deep proofs fit');
} catch (e) {
  problems.push(`screenshots: ${e.message}`);
}

await browser.close();
stop();

if (problems.length) {
  console.log('\nProblems:');
  for (const p of problems) console.log('✗', p);
  process.exit(1);
}
console.log(`\nAll ${results.length} browser checks passed; no console errors.`);
