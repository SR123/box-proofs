// Content of the help panel.

const A = (s) => `<i>${s}</i>`;
const X = A('X');
const Y = A('Y');
const Z = A('Z');

function inf(premises, conclusion, tag) {
  return `<span class="inf"><span class="prem">${premises}</span><span class="tag">${tag}</span><span class="bar"></span><span class="concl">${conclusion}</span></span>`;
}

function mini(top, bottom) {
  return `<span class="mini-box">${top}<span class="dots">⋮</span>${bottom}</span>`;
}

function card(name, body, note = '', wide = false) {
  return `<div class="rule-card${wide ? ' wide' : ''}"><div class="rname">${name}</div>${body}${note ? `<p class="note">${note}</p>` : ''}</div>`;
}

export function helpHtml() {
  const rules = [
    card('∧ intro', inf(`${X} &nbsp; ${Y}`, `${X} ∧ ${Y}`, '∧ intro'), 'The two lines may be the same line.'),
    card('∧ elim', `${inf(`${X} ∧ ${Y}`, X, '∧ elim')} &nbsp; ${inf(`${X} ∧ ${Y}`, Y, '∧ elim')}`),
    card('→ intro', inf(mini(X, Y), `${X} → ${Y}`, '→ intro'), 'Open a box assuming X, reach Y, close the box.'),
    card('→ elim', inf(`${X} &nbsp; ${X} → ${Y}`, Y, '→ elim'), 'Modus ponens. Write the line with X first: → elim 3,1.'),
    card('line k (copy)', inf(X, X, 'line k'), 'Repeat an earlier line that is still in scope, for instance to end a box.'),
    card('¬ intro', inf(mini(X, '⊥'), `¬${X}`, '¬ intro')),
    card('¬ elim', inf(`${X} &nbsp; ¬${X}`, '⊥', '¬ elim'), 'First the line with X, then the line with ¬X.'),
    card('contra', inf('⊥', X, 'contra'), 'From ⊥ conclude anything. Jape calls this contra (constructive).'),
    card('∨ intro (left) and (right)', `${inf(X, `${X} ∨ ${Y}`, '∨ intro')} &nbsp; ${inf(Y, `${X} ∨ ${Y}`, '∨ intro')}`, '(left) keeps the left side: from X get X ∨ Y. (right) keeps the right side: from Y get X ∨ Y.'),
    card('∨ elim', inf(`${X} ∨ ${Y} &nbsp; ${mini(X, Z)} &nbsp; ${mini(Y, Z)}`, Z, '∨ elim'), 'Proof by cases: both boxes end with the same Z.', true),
    card('contra (classical)', inf(mini(`¬${X}`, '⊥'), X, 'contra (classical)'), 'Reductio ad absurdum. Only in the full rules.'),
    card('↔ intro and ↔ elim', `${inf(`${X} → ${Y} &nbsp; ${Y} → ${X}`, `${X} ↔ ${Y}`, '↔ intro')}<br>${inf(`${X} ↔ ${Y}`, `${X} → ${Y}`, '↔ elim')}`, '↔ elim also gives Y → X. Only in the full rules.'),
  ].join('');

  return `
  <h3>How to use it</h3>
  <p>Pick an exercise or type your own sequent. The proof starts with the premises at the top and the goal at the bottom. The dots <b>⋮</b> mark a gap that still has to be filled.</p>
  <ul>
    <li><b>Select the goal</b> you want to work on (click the line or the dots above it). The current goal is shaded in teal.</li>
    <li><b>Work backwards</b> with an <i>intro</i> rule: it acts on the goal. For example → intro on <i>A</i> → <i>B</i> opens a box assuming <i>A</i> with the new goal <i>B</i>.</li>
    <li><b>Work forwards</b> with an <i>elim</i> rule: select one or more lines above the goal (they turn blue) and choose the rule. The new line appears just above the gap.</li>
    <li>When a goal matches a line it can use, it is closed for you, by a copy step <i>line k</i> if needed.</li>
    <li>Greyed-out rules do not apply right now; click or tap one to see why. Hover over or tap a justification to see the lines it uses.</li>
    <li><b>Hint</b> gives help in three levels, <b>Moves</b> lists the sensible moves with ✓ (leads to a proof) or ✗ (dead end), and <b>Show me</b> builds the whole proof step by step. With <b>Guided</b> ticked, the moves are listed after every step.</li>
    <li><b>Present</b> (or <kbd>P</kbd>) shows a larger proof for the projector and moves the exercises into a drawer.</li>
  </ul>

  <h3>The rules</h3>
  <div class="rules-grid">${rules}</div>

  <h3>The box rule</h3>
  <p>A box starts with an assumption. Lines inside a box may use lines above them, inside or outside the box. Once a box is closed, its lines are <b>out of bounds</b>: no line below the box may use them. Lines that the selected goal cannot use are shown faded.</p>
  <p>A box can only be closed by → intro, ¬ intro, ∨ elim (a pair of boxes) or contra (classical), and the closing line comes straight after the box. Premises come first, outside all boxes, and the last line is the conclusion, outside all boxes.</p>

  <h3>Strategy</h3>
  <ol>
    <li><b>Work backwards from the principal connective of the goal.</b> A goal <i>X</i> → <i>Y</i>: → intro. <i>X</i> ∧ <i>Y</i>: ∧ intro. ¬<i>X</i>: ¬ intro. These steps never go wrong.</li>
    <li><b>Work forwards from the premises.</b> Take conjunctions apart with ∧ elim, and use → elim when you have both <i>X</i> and <i>X</i> → <i>Y</i>.</li>
    <li><b>A disjunction above the goal?</b> Try ∨ elim: argue by cases.</li>
    <li><b>A disjunction as the goal?</b> ∨ intro, but only if you can prove one side as it stands; otherwise first use the lines above.</li>
    <li><b>Stuck, with ⊥ in sight?</b> If two lines contradict each other, ¬ elim gives ⊥ and contra gives any goal.</li>
    <li><b>Still stuck?</b> With the full rules, contra (classical): assume the negation of the goal and aim for ⊥.</li>
  </ol>

  <h3>Typing formulas</h3>
  <table class="kbd-table">
    <tr><td>→</td><td><code>-&gt;</code> <code>=&gt;</code> <code>implies</code></td><td>∧</td><td><code>&amp;</code> <code>/\\</code> <code>^</code> <code>and</code></td></tr>
    <tr><td>∨</td><td><code>|</code> <code>\\/</code> <code>or</code></td><td>¬</td><td><code>~</code> <code>!</code> <code>-</code> <code>not</code></td></tr>
    <tr><td>↔</td><td><code>&lt;-&gt;</code> <code>&lt;=&gt;</code> <code>iff</code></td><td>⊥</td><td><code>_|_</code> <code>bot</code> <code>false</code></td></tr>
    <tr><td>⊢</td><td><code>|-</code></td><td></td><td></td></tr>
  </table>
  <p>¬ binds tightest, then ∧, then ∨, then →, then ↔, and → groups to the right: <i>A</i> → <i>B</i> → <i>C</i> means <i>A</i> → (<i>B</i> → <i>C</i>). Atoms are letters such as <i>A</i>, <i>B</i>, <i>p</i>, <i>q</i>. Premises are separated by commas.</p>

  <h3>Keyboard</h3>
  <table class="kbd-table">
    <tr><td><kbd>↑</kbd> <kbd>↓</kbd></td><td>move between proof lines (after clicking a line or tabbing into the proof)</td></tr>
    <tr><td><kbd>Enter</kbd> or <kbd>Space</kbd></td><td>select the goal, or select or unselect a line</td></tr>
    <tr><td><kbd>Esc</kbd></td><td>clear the selected lines, close a dialogue or a tip</td></tr>
    <tr><td><kbd>Ctrl</kbd>/<kbd>⌘</kbd> + <kbd>Z</kbd></td><td>undo</td></tr>
    <tr><td><kbd>Ctrl</kbd>/<kbd>⌘</kbd> + <kbd>Shift</kbd> + <kbd>Z</kbd>, <kbd>Ctrl</kbd> + <kbd>Y</kbd></td><td>redo</td></tr>
    <tr><td><kbd>H</kbd> <kbd>M</kbd> <kbd>S</kbd></td><td>hint, moves, show me</td></tr>
    <tr><td><kbd>1</kbd> … <kbd>9</kbd></td><td>use a move from the list of moves</td></tr>
    <tr><td><kbd>P</kbd></td><td>Present: larger proof for the projector</td></tr>
    <tr><td><kbd>←</kbd> <kbd>→</kbd></td><td>previous and next step in Show me</td></tr>
    <tr><td><kbd>?</kbd></td><td>this help</td></tr>
  </table>

  <h3>About</h3>
  <p>Box proofs are <b>sound</b>: every sequent with a proof is valid. So when the truth table finds a row where the premises are true and the goal is false, no proof can exist, and the app shows that row instead. For valid sequents the built-in prover always finds a proof with the course rules (using contra (classical) only where it is needed).</p>
  <p>The module also uses <b>Jape</b>, by Richard Bornat and Bernard Sufrin, which is the reference tool for these proofs. This app follows the same rules and justification style, and adds explanations of the strategy.</p>`;
}
