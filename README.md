# Box proofs

A web app for building and checking Fitch-style box proofs in propositional logic, written for ECS407U Logic and Discrete Structures at Queen Mary University of London.

**Use it online: <https://sr123.github.io/box-proofs/>**

Students build natural deduction proofs as nested boxes, in the same layout and with the same justifications as the lecture slides and Jape. The app explains the strategy as it goes: it says which moves still lead to a proof and which are dead ends, gives hints in three levels, and can build a whole proof one step at a time.

It is a static site: plain HTML, CSS and JavaScript modules. There is no build step, nothing to install, and it makes no network requests while running (no CDN, no analytics, no cookies). `localStorage` is only used for conveniences: the ✓ marks of solved exercises, a typed sequent, the Guided setting, Present mode, the text size and the colour theme.

## Using it

The plain address of the app always opens the **start page**: the first and-game exercise with an empty proof. Clicking the title **Box proofs** at the top left goes back there at any time, so a demo in a lecture starts the same way every time. **Start afresh**, at the bottom of the exercise list, also clears the ✓ marks of solved exercises (click it twice to confirm); the address `?fresh=1` does the same. Present mode, the text size and the colour theme are kept.

1. Pick an exercise on the left (under **Exercises** on smaller screens and in Present mode), or type your own sequent under **Your own sequent** (for example `A → B, ¬B ⊢ ¬A`, or in ASCII `A -> B, ~B |- ~A`).
2. The proof starts with the premises at the top and the goal at the bottom. The dots **⋮** mark a gap that still has to be filled.
3. **Select a goal** (it is shaded in teal) and choose a rule:
   - **Work backwards** with an intro rule, which acts on the goal. For example → intro on `A → B` opens a box assuming `A`, with the new goal `B`.
   - **Work forwards** with an elim rule: select one or more lines above the goal and choose the rule. The new line appears just above the gap.
4. A goal is closed automatically when a line it may use has the same formula: directly when that line is just above it, otherwise by a copy step `line k`.
5. Rules that do not apply are greyed out; click or tap one and a short note next to it says why. Hover over or tap a justification to shade the lines it uses. Lines that the selected goal may not use because they sit inside a closed box are faded.

Help while proving:

- **Hint**: three levels: (1) work backwards or forwards, (2) which rule, (3) do it.
- **Moves** (the "next step" list): the sensible moves for the selected goal, grouped into *work backwards* and *work forwards*. Each is marked ✓ (still leads to a proof) or ✗ (dead end) and says in a few words what it does; **Why?** opens a one- or two-sentence explanation, and a ✗ comes with the reason, often a truth-table row. When several moves lead to a proof, the guide says there is a choice. A safe step that the suggested proof does not need is shown muted.
- **Guided** (checkbox): show the move list after every move; the rule buttons are then marked ✓ or ✗ too.
- **Show me**: builds the rest of the proof step by step (Previous / Next / Play), in the order a person would work: backward steps first, forward steps when a line is needed. Play pauses at choice points and shows the alternatives. Every step it takes is one of the ✓ moves of the move list.
- **Solve**: lets the prover fill in the rest at once (Undo takes it back).
- **Present** (button in the header, or the P key): for the lecture room. The proof is larger, rows are tighter, the guide is a narrow column on the right, and the exercises move into a drawer. The setting is remembered.

If a typed sequent is not valid, the app shows a truth-table row in which the premises are true and the goal is false. Box proofs are sound, so no proof can exist. For an exercise in the library marked as invalid (a "Can you prove it?" exercise) the verdict is kept back: the student can try to build a proof, or pick a truth-table row and ask whether it is a counterexample. Hint, Moves, Show me and Solve reveal the answer.

If the sequent is valid but the chosen rule set is too small (it needs contra (classical)), the app says so and offers a button to switch to the full rules.

**Share and export** copies a link to the current problem, copies the proof as plain text (boxes drawn with `│ ┌ └`) or as a self-contained TikZ picture for LaTeX, or downloads it as an SVG. **Check a proof** (in the header, and in the Share and export menu) reads a proof pasted as text and checks it line by line. If the proof is correct but uses rules outside the current rule set, it says which; opening it in the editor widens the rule set, and the exercise is then not marked as solved.

On a phone the main actions sit in a bar at the bottom of the screen: Undo, Hint and the rules that apply, or Previous / Next / Play while Show me runs. The rule set, Guided, Share and export and the text size are under **More**. A deep proof that is too wide for the screen puts each justification under its formula.

### Keyboard

| Keys | Action |
| --- | --- |
| ↑ ↓, Home, End | move between proof lines |
| Enter, Space | select the goal, or select/unselect a line |
| Esc | clear selected lines, close dialogues and tips |
| Ctrl/⌘ + Z | undo |
| Ctrl/⌘ + Shift + Z, Ctrl + Y | redo |
| H, M, S | hint, moves, show me (N also lists the moves) |
| 1 … 9 | use a move from the move list |
| ← → | previous / next step in Show me |
| P | Present on or off |
| ? | help |

## Rules and notation

The justifications follow Jape:

| Rule | From | Gives | Written |
| --- | --- | --- | --- |
| premise | | a premise of the sequent | `premise` |
| assumption | | opens a box | `assumption` |
| copy | line k (still in scope) | the same formula | `line 1` |
| ∧ intro | X, Y (may be the same line) | X ∧ Y | `∧ intro 2,3` |
| ∧ elim | X ∧ Y | X, or Y | `∧ elim 1` |
| → intro | box from X to Y | X → Y | `→ intro 2–4` |
| → elim | X, X → Y | Y | `→ elim 3,1` (first X, then X → Y) |
| ¬ intro | box from X to ⊥ | ¬X | `¬ intro 2–5` |
| ¬ elim | X, ¬X | ⊥ | `¬ elim 3,1` (first X, then ¬X) |
| contra | ⊥ | any formula | `contra 4` |
| ∨ intro | X | X ∨ Y, or Y ∨ X | `∨ intro 3` |
| ∨ elim | X ∨ Y, box X … Z, box Y … Z | Z | `∨ elim 1,2–4,5–7` |
| contra (classical) | box from ¬X to ⊥ | X | `contra (classical) 2–6` |
| ↔ intro | X → Y, Y → X | X ↔ Y | `↔ intro 2,3` |
| ↔ elim | X ↔ Y | X → Y, or Y → X | `↔ elim 1` |

**The box rule.** A box starts with an assumption. Once a box is closed, its lines are out of bounds: nothing below the box may use them. A box can only be closed by → intro, ¬ intro, ∨ elim (a pair of boxes) or contra (classical), and the closing line comes straight after the box. Premises come first, outside all boxes, and the last line is the conclusion, outside all boxes.

**Rule sets.** The games of the course are cumulative. Premises, assumptions and copying a line are always allowed.

| Rule set | Adds |
| --- | --- |
| And-game | ∧ intro, ∧ elim |
| Implication game | → intro, → elim |
| Not-game | ¬ intro, ¬ elim, contra |
| Or-game | ∨ intro, ∨ elim |
| Full rules (classical) | contra (classical), ↔ intro, ↔ elim |

Each exercise sets its rule set; the **Rule set** menu widens it. A rule set too small for the connectives of the sequent cannot be chosen.

**Typing formulas.** Atoms are letters or short names (`A`, `B`, `p`, `q`, `p1`). Connectives can be typed in Unicode or ASCII:

| | Unicode | ASCII |
| --- | --- | --- |
| implies | → | `->` `=>` `implies` |
| and | ∧ | `&` `/\` `^` `and` |
| or | ∨ | `\|` `\/` `or` |
| not | ¬ | `~` `!` `-` `not` |
| if and only if | ↔ | `<->` `<=>` `iff` |
| falsum | ⊥ | `_\|_` `bot` `false` |
| turnstile | ⊢ | `\|-` |

¬ binds tightest, then ∧, then ∨, then →, then ↔. → groups to the right, so `A → B → C` means `A → (B → C)`. Formulas are displayed as on the slides: a binary formula inside a binary formula is always bracketed, as in `A → (B → A)` and `(A ∧ B) → (B ∧ A)`, and there are no outer brackets. A sequent without ⊢ is a goal with no premises.

## Linking to an exercise

The address of the page describes the problem, so links from a module page open the right exercise:

| Parameter | Meaning | Example |
| --- | --- | --- |
| `ex` | an exercise from the library, by id | `?ex=imp-2` |
| `s` | any sequent, Unicode or ASCII (URL-encoded) | `?s=A%E2%88%A7B%20%E2%8A%A2%20B%E2%88%A7A` or `?s=A%26B%7C-B%26A` |
| `game` | rule set: `and`, `imp`, `not`, `or`, `full` | `?s=...&game=full` |
| `mode` | `guided` shows the move list after every move; `showme` starts Show me | `?ex=or-2&mode=guided` |
| `solve` | `0` hides Solve and Show me (for tutorials) | `?ex=imp-3&solve=0` |
| `present` | `1` turns Present on, `0` off | `?ex=or-4&present=1` |
| `embed` | compact layout for an iframe | `?ex=imp-2&embed=1` |
| `fresh` | `1` opens the start page and clears the ✓ marks (for a clean demo) | `?fresh=1` |

For example:

- `https://sr123.github.io/box-proofs/?ex=imp-2` opens "One box, one copy" (⊢ A → (B → A)).
- `https://sr123.github.io/box-proofs/?s=A%E2%86%92B%2C%20%C2%ACB%20%E2%8A%A2%20%C2%ACA&mode=guided` opens A → B, ¬B ⊢ ¬A in guided mode.
- `https://sr123.github.io/box-proofs/?s=p%20-%3E%20q%2C%20~q%20%7C-%20~p` uses ASCII.

The **Copy link** item under *Share and export* produces such a link for the current problem: for an exercise just `?ex=…` (plus `game=` if the rule set was changed), otherwise `?s=…`. A link to an unknown exercise id opens the first exercise and says so. Unencoded links such as `?s=A&B|-B&A` also work, but encoding `&` as `%26` is safer.

Exercise ids: `and-1` … `and-7`, `imp-1` … `imp-7`, `both-1` … `both-5`, `not-1` … `not-5`, `or-1` … `or-6`, `cl-1` … `cl-5` (see `js/exercises.js` for the full list).

## Embedding with an iframe

```html
<iframe src="https://sr123.github.io/box-proofs/?ex=or-4&embed=1"
        title="Box proof: proof by cases"
        width="100%" height="760" style="border: 0"></iframe>
```

`embed=1` hides the header, the exercise library, the export menu and the text-size buttons, and puts an "Open in the full app" link at the top. In a frame at least 900 px wide the guide sits beside the proof; in a narrower frame it comes straight after the proof. A height of 760 px shows the problem, the proof and the guide's buttons at any width from about 700 px up; the frame scrolls for longer proofs.

## Deploying on GitHub Pages

1. Create a repository and push the contents of this folder to its `main` branch (the folder with `index.html` at its top).
2. On GitHub: **Settings → Pages → Build and deployment → Source: Deploy from a branch → Branch: `main`, folder: `/ (root)`** → Save.
3. After a minute the site is at `https://<user>.github.io/<repo>/` (this one is at <https://sr123.github.io/box-proofs/>).

The `.nojekyll` file tells GitHub Pages to serve the files as they are.

To try it locally, serve the folder with any static server, for example

```sh
python3 -m http.server 8000
```

and open <http://localhost:8000/>. (Opening `index.html` directly from the disk does not work, because browsers do not load JavaScript modules from `file://` addresses.)

On a Mac you can instead double-click `preview-on-mac.command`: it starts the server and opens the app in Firefox (or the default browser).

## Adding exercises

Edit `js/exercises.js`. Each group has a title, a rule set (`game`) and a list of exercises:

```js
{ id: 'imp-8', title: 'A new one', sequent: 'A → B, B → C, C → D ⊢ A → D' },
```

- `id` is used in links (`?ex=imp-8`), so keep it short and do not change it once it has been shared.
- `sequent` may use Unicode or ASCII.
- Add `game: 'full'` to an exercise to override the group's rule set.
- Add `invalid: true` for a deliberate "Can you prove it?" exercise. (Any library exercise without a proof keeps its verdict back until the student asks; the tests check that exactly the exercises marked `invalid` have no proof.)

Run the tests afterwards (below): they check that every exercise has a proof, or a counterexample if it is marked `invalid`.

## How it works

- `js/formula.js`: parsing (Unicode and ASCII, with friendly error messages) and printing (Unicode, ASCII, LaTeX, HTML).
- `js/proof.js`: the proof model: partial proofs with open goals, moves (intro rules backwards, elim rules forwards), automatic closing of goals, line numbering.
- `js/checker.js`: an independent checker that works on a flat list of numbered, indented lines. It checks premises, the box rule, the shape of every rule, the references, and that every box is closed straight after it ends.
- `js/semantics.js`: truth tables (up to 14 atoms) and counterexamples.
- `js/intuitionistic.js`: Dyckhoff's contraction-free calculus G4ip, a decision procedure for intuitionistic propositional logic, used as an oracle.
- `js/prover.js`: the prover. A goal-directed search in the style of an intercalation calculus: intro rules backwards on the goal, elim rules forwards from the lines above, loop checking on (available formulas, goal), with G4ip pruning dead branches. It prefers natural steps (close by a line; → intro, ∧ intro and ¬ intro; ∧ elim and → elim; ∨ intro when one side follows; ∨ elim; and only then contra). When the available lines already contradict each other (so every goal follows and the oracle cannot prune), it aims for ⊥ and contra, proves ⊥ from a minimal set of contradicting lines, and drops case splits and → elim steps whose new line is never used; the proofs it writes have no unused lines. The right half of an ∧ intro may use the left half. If a sequent is classically valid but not intuitionistically, the goal is broken up with the invertible rules and the rest is proved with contra (classical): assume the negation of the goal and derive ⊥. By Glivenko's theorem this always works. For very large formulas a refutation tableau, written out with the course rules, is the fallback. Every search has a time limit of about 1.5 to 2 seconds, and the app says so if the limit is reached.
- `js/guide.js`: labels moves ✓/✗, explains them, gives hints, and turns the prover's proofs into a sequence of moves for Show me. A move is ✗ only if a goal it leaves behind really cannot be proved (decided by a truth table or G4ip). Moves that would only lead back to an earlier situation are left out, unless every move that still works does that (after a roundabout move from the rule panel); those are then shown and marked. Labelling the moves has one time budget of about 2 seconds. Show me plans one goal at a time from the current state, so later goals can use lines already written, and checks each step against the move list.
- `js/render.js`, `js/export.js`, `js/textformat.js`, `js/help.js`, `js/app.js`: drawing, export, the text format, the help panel and the user interface.

## Tests

Unit tests use Node's built-in test runner (Node 18 or later; nothing to install):

```sh
node --test tests/*.test.js      # or: npm test
```

They cover parsing and printing (round trips, precedence, brackets), the checker (the slide proofs, and wrong proofs such as the "spot the bug" proof), the prover (every exercise; a seeded battery of 320 random sequents over 2–4 atoms checked against truth tables; an intuitionistic battery checked against a plain search; a stress battery of larger formulas), the guided mode (random walks over ✓ moves always reach a complete, checked proof; ✗ moves really are dead ends), and the exporters. `tests/regressions.test.js` holds a test for each problem found in review: contradicting lines (short proofs, no unused lines, no timeouts in a 400-sequent or-game battery), roundabout moves from the rule panel, the time budget of the move list, Show me steps that are always listed ✓ (150 random sequents), more than 14 atoms, the wording of dead ends, hints and move titles, the ASCII parser, unfinished proofs in the text format, rule sets of imported proofs, and export details.

`qa/browser-check.mjs` drives the app in Chromium with [Playwright](https://playwright.dev/), which is not a dependency of the app: install it separately (`npm install -g playwright`, then `npx playwright install chromium`) or point `PLAYWRIGHT_MODULE` at an existing copy. It serves the folder with `python3 -m http.server`, builds proofs by clicking and with the keyboard, runs guided mode and Show me, opens shared links, embeds the app in an iframe, tries the exporters and the checker, checks that tips and the guide are in view at 1280×720 and 1024×768, tries Present mode, the phone tray, the "Can you prove it?" exercise and the start page (title link, Start afresh, `?fresh=1`), fails on any console error, and saves screenshots to `qa/` (1280×800 and 390×844 in light and dark, plus the other sizes).

```sh
node qa/browser-check.mjs
```

## Credits and licence

The module also uses Jape, by Richard Bornat and Bernard Sufrin, which is the reference tool for these proofs. This app follows its rules and justification style.

Released under the MIT licence (see `LICENSE`), copyright 2026 Søren Riis. The copyright holder may change the licence.
