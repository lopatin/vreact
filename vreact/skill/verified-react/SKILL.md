---
name: verified-react
description: Build React components and apps that are formally verified in Lean 4. Use when the user wants verified/proven-correct React code, formal guarantees about component state (invariants that can never break), "correct by construction" UI logic, or asks to synthesize React components from a specification. Writes components in VTS (a verified TypeScript+TSX subset with requires/ensures/invariant contracts), checks every proof obligation with `vreact verify` (translation to Lean 4 + a semantic model of React state, batching, rendering, effects and reconciliation), fills `hole<T>()` placeholders with `vreact synth`, and iterates until the whole app has a kernel-checked certificate.
---

# Verified React (vreact)

You write **ordinary React + TypeScript** in a verifiable subset (VTS) with
contracts. `vreact verify` translates it to Lean 4, where a semantic model of
React (update queues and batching, snapshot vs. stale closures, proof-carrying
render trees, effects, reconciliation, parent/child callback contracts) turns
every component into proof obligations that Lean's kernel checks. The same
`.tsx` runs unchanged in the browser.

**Done means:** `vreact verify` prints `✔ VERIFIED` and the app certificate's
axioms are exactly `propext, Classical.choice, Quot.sound`. Anything else —
`INCOMPLETE`, `UNCHECKED`, `TRUSTED`, `ASSUMES`, `VERIFIED*`, `sorryAx`, `VReact.assumed` (`assumed`) — is not done;
say so plainly when reporting.

The tool lives in this skill's directory under `tool/` (the `vreact` package):
`node <skill>/tool/bin/vreact.js verify` (or `npx vreact verify` once installed
in the project). Read `reference/language.md` before writing VTS and
`reference/obligations.md` when an obligation fails. The formal model is in
`tool/docs/SEMANTICS.md`; a complete worked example (spec-first model,
synthesis, top-down App with trusted stubs, bugs caught, final certificate) is
`tool/docs/WALKTHROUGH.md`. The repository that contains the tool also has a larger
example, `examples/options-chain`, with its walkthrough `docs/OPTIONS_CHAIN_WALKTHROUGH.md`:
it grows a verified app with a `requires` on dispatched actions, a Lean proof file, state on
Maps and Sets, and generic helpers.

## Setup (once per machine / project)

```bash
bash <skill>/scripts/setup.sh                 # checks Node ≥ 22.6, Lean 4 (elan), builds the Lean library
bash <skill>/scripts/setup.sh /path/to/app    # also: npm i the tool into the app, write vreact.json, Lean editor files
```

Installing Lean (elan, ~400 MB) changes the user's machine: ask first if it is
missing. All the app needs from npm is that `vreact` (and `react`, `@types/react`)
resolve from its folder — `npm i <tool>` or a symlinked `node_modules` both work. The app needs `"strict": true`, `"jsx": "react-jsx"` and `"lib": ["ES2023", "DOM"]` in tsconfig (no other
`jsxImportSource`, no JSX pragmas, no `@ts-ignore`/`@ts-expect-error`/`@ts-nocheck` in verified files) and `vreact.json`
(`{"src":"src","exclude":["main.tsx"],"proofs":"proofs","out":".vreact"}`).
Keep `main.tsx` outside the verified program, and mount the app with `createRoot` (or
`hydrateRoot`): certificates assume React 18's concurrent root, whose automatic batching
the model has; a legacy `ReactDOM.render` root renders between two setters of a timer. `"out"` must be a directory of its
own (vreact replaces its `VTS/`, `Proofs/` and `.lake/`): not the app folder, `src` or `proofs`,
nor containing one, nor inside `proofs` (inside `src` is fine: `"src": "."` with `.vreact`). Files
named `*.test.*`/`*.spec.*` in `src` are skipped as tests (not verified; a verified file must not
import one). No `"references"` in tsconfig.json (merge Vite's `tsconfig.app.json` into it),
`"extends"` only to a project file named in full (`"./tsconfig.base.json"`), no symbolic links in
`src`, no `?`, `#`, `%` or `\` in file paths, no object `"browser"` field in a package.json.

Lean editors (WebStorm/IntelliJ with `lean4ij`, VS Code with the Lean 4 extension):
`setup.sh /path/to/app` and every `vreact verify` write `lean-toolchain` (the tool's Lean
version) and a `lakefile.toml` that requires the generated `.vreact/` project into the app
folder, and add `.lake/` and `lake-manifest.json` to its `.gitignore`. Run `vreact verify` once,
then open the **app folder** as the editor's project: `proofs/*.lean` get live checking, with
`import VTS.<Module>.Defs` resolved against the last `vreact verify` (re-run it after changing
the TypeScript). From a shell, `lake lean proofs/<Module>.lean` in the app folder checks one
proof file the same way. The editor is a convenience: `vreact verify` stays the source of truth.
Let `vreact verify` finish before opening a proof file: when `.vreact/` is newer than its build
(after `vreact translate`, or a verify that was interrupted), the editor first builds the
imported `VTS.<Module>.Defs` itself, proving that module's obligations, which can take minutes
behind a bare progress bar. Do not run `vreact verify` while the editor is doing that (both build
`.vreact/`); a build the editor made is not evidence for `vreact verify`, which then removes it and
builds `.vreact/` again (it counts only builds it made itself). `lake build` in the app folder
builds nothing (the app's package has no targets).
vreact keeps its own `lakefile.toml` (first line `# vreact: Lean editor support`) and
`lean-toolchain` up to date, and never writes either over a `lakefile.toml` without that line
or a `lakefile.lean` (the user's own Lean project). Such a lakefile needs a `[[require]]` of the
package `vts` at the `"out"` directory (`require vts from ".vreact"` in a `lakefile.lean`);
`setup.sh` says so when it has none.

## The workflow

Work in small verified increments; run `vreact verify` after every meaningful
change (it is incremental and usually takes seconds).

1. **Model first.** Put state types, the invariant (a `boolean` function such as
   `wellFormed(b)`) and pure operations in a `.ts` module. Give operations
   contracts before bodies:
   * reducers and anything called from a functional update or `dispatch` must be
     **total in the state** — no `requires` about it; state invariant preservation as
     `ensures((r: T) => implies(inv(s), inv(r)))`. A reducer may have a `requires`
     about the **action** alone (`requires(validAction(a))`): it is proved at every
     `dispatch(…)` site, so bad actions are ruled out statically, not guarded at run time;
   * add **functional** postconditions (what the operation achieves), not only
     invariant preservation — otherwise `return s` satisfies the spec;
   * mark big operations `/** @opaque */` so callers reason by contract.
2. **Synthesize / implement.** Leave `return hole<T>();` and run
   `vreact synth src/model.ts --write`. If it returns a trivial program
   (`return s`), the spec is too weak — strengthen it. Synth builds
   *straight-line* expressions: field updates `{ ...s, f: e }` (one or two
   fields), record/variant literals, `[...xs, e]`, `[...xs, ...ys]`,
   `xs.filter(x => x.k !== v)`, `xs.map(x => x.k === v ? { ...x, f: e } : x)`,
   calls of the module's total helpers (generic ones at the hole's types),
   `± 1` and comparisons — smallest first,
   up to size 9. Each hole costs up to ~60 s of search (candidates are built as
   they are tested, and the limit holds while one is tested; one candidate's
   tests get at most 5 s: one cut off after passing the tests that ran goes to
   Lean after the candidates whose tests finish, or once 3 such are held back)
   plus up to 5 Lean checks
   of candidates that pass the random tests; a function with n holes takes up
   to about n times that. Holes go in code only: a hole inside a contract
   (`requires`, `ensures`, `invariant`, `decreases`, `callbackRequires`,
   `assert`, `assume`) is never filled — the contract is what the holes are
   filled against, so a fill proved against it could be vacuous
   (`requires(false)`) — and its function is not searched: write the contract
   by hand. Likewise a function that a contract calls (directly or through
   other functions) and that has no `ensures` of its own is not filled: Lean
   would check its fill against nothing (`true` would be "proved") and the fill
   would become part of that contract — give it an `ensures` or write it. The
   functions that module-level code calls (`export const N: int = f(1);`) are
   filled first: while one has a hole, the constants declared after that call
   stay uninitialized in the tests, and inputs that read one are skipped.
   Guarded updates (`if … return s;`)
   are not in the grammar: write the guard by hand and leave a hole in each
   branch (or `case`) — the holes of one function are filled and proved
   together (holes in different branches or cases are searched once each,
   whatever the others are filled with). `✔ proved by Lean` means Lean checked
   the whole function; `(relative to …)` — `"status": "proved-relative"` with
   `relative_to` under `--json` — means the proof assumes those @trusted
   contracts or `assume(…)` facts. A `? not proved` line names what kept Lean
   from checking it (often a failing obligation elsewhere in the module or an
   import: fix that first; when it is a helper that a fill calls — the
   candidate or another hole's fill — the fills that do not call it are tried
   next); a contract whose statement depends on a function
   that still has a hole (through calls, their bodies and `requires`; not
   through `@trusted` bodies) is reported as such: fill that function first. Synth never edits the
   file while searching; `--write` writes only proved fills (and drops the imports, and the
   file's own non-exported types, that only the filled `hole<T>()` calls used: Lean checks that
   exact text). A field whose name is not an identifier (`"my-field"`) is never read (VTS has no
   `p["my-field"]`). Maps and Sets only grow in its
   grammar (`new Map(m).set(k, v)`, `new Set(s).add(x)`): a fill that deletes is written by
   hand. The random tests are reproducible: each hole's inputs come from a seeded generator
   (`--seed N` picks another seed, default 1), so two runs test the same inputs and print the
   same counterexamples; only the 60 s limit depends on the machine. (The tests only filter
   candidates: Lean proves every fill.)
3. **Reducer** — a `switch` over a discriminated-union action type, total in the
   state (a `requires` on the action is checked at each dispatch), delegating to
   the model; `ensures` that it preserves the invariant.
4. **Components top-down.** Write the root for real; stub children as
   `/** @trusted */` with only their props type and contracts (`requires`,
   `callbackRequires`) and a placeholder body. Verify: the root becomes
   `VERIFIED*` (relative to stubs). Then implement children one by one until
   every component is `VERIFIED` and the certificate is clean.
   (Bottom-up — leaves first — works equally well; mix as convenient.)
5. **Read every failure** (see below), fix the *code* when it is wrong, the
   *spec* when it is too weak or too strong, and only then help the prover.
6. **Run the app** (`npm run dev`) and exercise it — verification covers the
   model, not the CSS.

## Writing components (essentials — full rules in reference/language.md)

```tsx
import { useState, useReducer } from "react";
import { requires, invariant, callbackRequires, distinct, type int } from "vreact/spec";

type ItemListProps = { readonly items: readonly Item[]; readonly onPick: (id: int) => void };

export function ItemList(props: ItemListProps) {
  requires(distinct(props.items, (i) => i.id));                       // props precondition
  callbackRequires(props.onPick, (id) => props.items.some((i) => i.id === id)); // promise to parent
  const [open, setOpen] = useState<boolean>(false);                    // hooks first, unconditional
  invariant(true);                                                     // state invariant (after hooks)
  return (
    <ul>{props.items.map((i) => (
      <li key={i.id}><button onClick={() => props.onPick(i.id)}>{i.name}</button></li>
    ))}</ul>
  );
}
```

* Use `int` for integers (counts, ids, cents); `number` is a float the prover knows nothing about (opaque: no arithmetic, comparison or `Math.*` facts). A division `a / b` needs a divisor that is not zero (`requires(b !== 0)` or a guard `b === 0 ? … : a / b`; a nonzero literal divisor needs nothing): `1 / -0` is `-Infinity`, and VTS values do not keep the sign of zero.
* `implies(a, b)` is a function call: JS evaluates `b` even when `a` is false. In `requires`, `invariant`, `assert` and `assume`, which run at every call or render, `b` must be safe on its own (no index, `!` or divisor that needs `a`): write `!a || b`, e.g. `requires(xs.length === 0 || xs[0] > 0)`. Only in `ensures` lambdas and the expression body of `callbackRequires` lambdas (the app never runs them; `vreact synth`'s tests evaluate an ensures' `implies(a, b)` as `!a || b`, as the prover reads it) may `b` rely on `a`: `ensures((r: T) => implies(xs.length > 0, r === xs[0]))`.
* Helpers used at several types may be generic top-level functions:
  `<K extends int | string>` to compare keys (`===`, `includes`, `distinct`),
  `<T extends { readonly id: int }>` to read fields; values of a type parameter are
  otherwise abstract. Write `f<int>(…)` when a type parameter cannot be inferred.
  No generic type aliases, components or arrows, no `@trusted` generics, and no
  callback parameters (`p: (x: T) => boolean`): use a field constraint.
* State is immutable: spread, `filter`, `map`, `toSorted`, `with` — never `push`/`sort`/property assignment.
* No recursion: a function may not call itself, nor a component render itself (`<Tree/>` inside
  `Tree`): render nested data from a flat array (rows with a depth field) with one `map`.
* Maps/Sets (`ReadonlyMap<int, Item>`, `ReadonlySet<string>`; keys int/string/boolean/enum, or
  `K extends int | string` in a generic helper such as `toggleIn<K>(s: ReadonlySet<K>, k: K)`):
  update a fresh copy — `new Map(m).set(k, v)`, or `const n = new Map(m); n.delete(k); return n;` —
  never state, props or parameters; consume iterators at once (`[...m.values()]`, `for…of`).
* Handlers may call setters, `dispatch`, and **at most one** parent callback per path —
  in their own statements, or in a local helper called as a statement (`bump();`) or as
  `const v = bump();`; never inside an array callback, a functional update, or an expression
  (`setN(bump())`). A callback implementation may ignore trailing arguments (`() => close()`).
* `setX(v)` uses the render snapshot; two of them in one handler do not compose — use
  `setX(prev => …)` when updates must accumulate.
* Effects/timers and continuous/default-priority handlers (`onMouseMove`,
  `onScroll`, `onTransitionEnd`, `onLoad`, …) must preserve the invariant from
  **any** state (stale closures): prefer functional updates there; effect deps
  must be exhaustive (and `useMemo`/`useCallback` deps): data paths — `[m]` for
  `m.has(k)`, never `[m.has]`. Cleanups only clear timers (and log / write `localStorage` /
  `document.title`; the arguments of such writes are checked everywhere, like any
  expression; in a cleanup they and a timer's delay are data, reading methods only: no
  `xs.push`, setters or helpers). In such a component, clicks etc. must also be safe on top
  of their pending updates (React rebases): guard inside `setX(p => …)`.
* Closures read `let`s when they run: do not reassign a `let` after creating a
  handler/helper/updater that reads it (`const xNow = x;` first), and never assign
  an outer `let` inside a callback. A helper or handler may read a `const` declared
  after it if it is used (called, attached) after that declaration; a `useEffect`,
  `useCallback` or `useMemo` function may not (its deps cannot list it): declare
  what a hook reads before the hook. State, too, exists only from its `useState`
  on (put the hooks first; an `invariant` reads only the state above it). Local
  functions cannot be recursive. A timer callback may read the effect body's
  `const`s declared before `setTimeout`/`setInterval`.
* Module constants run in source order when the module loads: declare a constant
  above every constant (or `assert`) whose initialiser uses it, also through a
  function call. `export default` only a name, never an expression.
* Names mean what they resolve to: a local `undefined`, an import named `Math`
  or a project type named `int` is that binding, not the builtin. No `declare`,
  `declare global`/`module`, namespaces or project `.d.ts` files.
* Import verified modules by their relative path (`"./model"`, not a tsconfig
  `paths` alias), and hooks from `"react"`. Re-export imported types with
  `export type { T }` (VTS checks with `isolatedModules`). No `@ts-ignore`,
  `@ts-expect-error` or `@ts-nocheck` (any spelling), no `@jsx…` pragmas and no
  `@__PURE__`-style annotations anywhere in a file: fix the type error instead.
* tsconfig: `"strict": true` and nothing that weakens it; unknown or
  check-disabling compiler options (`noCheck`, …) are rejected by name.
* Read event fields in the handler itself: `const v = e.target.value;
  setX((p) => … v …)` — a functional update runs after the event's dispatch
  (`e.currentTarget` is null then), so reading `e.…` inside it is rejected.
  Put the handler on the control whose field it reads (`<input onChange>`:
  `e.target.value`; `e.key` in `onKeyDown`): fields are checked against the element
  and handler prop, not against the type annotation of `e`.
* Invariants must not depend on props that can change (React keeps state across
  prop changes): clamp when rendering instead.
* Lists need `key={…}` with provably distinct keys (usually from an invariant).
  Keyed siblings in one element (`<Viewer key=…/><Notes key=…/>`) need distinct keys
  too, compared as strings (`key={1}` = `key="1"`): use distinct literal prefixes or
  suffixes (`` key={`viewer-${id}`} ``, `` key={`notes-${id}`} ``; `` key={`${id}-title`} ``,
  `` key={`${id}-body`} ``).
* One native event may reach only one discrete handler: no `onX` element may wrap
  a handler fired by the same native event (`onClick` around a checkbox's
  `onChange`: both run on click) or a user component, and one element may not
  combine such handlers (checkbox `onClick` + `onChange`; `onInput` + `onChange`).
  A click's activation counts too: no `onClick` on, around or inside a submit
  button of a form with `onSubmit` (use `type="button"`) or a `<label>`, and no
  `<label>` or nested button inside such a submit button.
  A `<select>` holds only `<option>`/`<optgroup>` elements, an `<option>` only
  text: no other element or user component inside (a control there would run
  the select's `onChange`).
  `onFocus`/`onBlur`/`onInvalid` must be robust (no parent callbacks), and the focus
  handlers of an `autoFocus` element, or of an element around one, may not update state
  unless every `autoFocus` element of the component is in its only `return`, not under
  a condition or in a list, with no `key` on it or around it, and the component renders
  no other component.
* `name`/`id` of form controls (`<input>`, `<button>`, `<select>`, `<textarea>`,
  `<output>`, `<fieldset>`), `<img>`, `<object>`, and `name` of `<form>`, `<iframe>`,
  `<embed>`: no name React uses on forms or the document (`parentNode`, `removeChild`,
  `createElement`, `value`, `type`, `length`, …; `name`, `title`, `id`, `submit` are
  fine on controls) nor `_…`/`on…`, and statically bounded (a literal, a choice between
  literals, an enum, or a string with a literal part holding a character other than
  letters, digits, `_`, `$`: `` `qty-${id}` ``). A written `id` of any element may not
  be a global React reads (`nodeName`, `type`, `jest`, …).

## Reading results

`vreact verify` reports, per component/function (and per constant, when not
`VERIFIED`): `VERIFIED`, `VERIFIED*` (own obligations proved, relies on
`@trusted` contracts), `TRUSTED` (`@trusted`; also an item relying on an axiom from
outside the translation, or on a user-proof declaration that uses `VReact.assumed`
itself, should one get past the proof checks — the `↳` line names it),
`ASSUMES` (relies on the program's `assume(…)` facts),
`INCOMPLETE` (a failed or unchecked obligation, `hole()`/`sorry`, a declaration
Lean could not finish, or it relies on an item that is not verified — the line
under it names the reason, e.g. `↳ it uses clamp (src/lib.ts), which is not
verified: an obligation of it failed`), `UNCHECKED` (Lean never got to it: a
Lean build/import error or an internal error stopped its file), plus each failed obligation as
`file:line:col [kind] description` followed by the Lean goal. In the goal, the
hypotheses are what is known (props precondition, invariant, branch
conditions, `h_…` facts); `⊢ False` after `grind` means the facts were
insufficient — often a real counterexample is visible in them (e.g. `h : total = 0`).
Goals are shortened to 18 lines; `vreact verify --full` prints them completely (`--json`
has both `lean` and `leanFull`). A long goal keeps its conclusion `⊢ …` (at most 3 lines) and
the short hypotheses next to it, which usually decide the case; what it leaves out is named and
counted by a line that ends in `--full shows it` (or `them`): the contract instances of called
functions (`hcontract, hcontract_1 : …  (2 contract instances, 40 lines: …)`), let-definitions
that span several lines (`center, atm := …  (2 definitions, 8 lines: …)`), other long
hypotheses (only as many as needed; the hypothesis right above the conclusion, often the
negated goal or the last case split, stays whole when it fits; one too long to fit is one line
where it was), and last the hypotheses farthest from the conclusion (`… (12 earlier
hypotheses: E, props, κ, …)`). Every other line is a whole line of Lean's text. `vreact explain <file>` prints the generated
Lean; `.vreact/` is an ordinary Lake project, so `cd .vreact && lake env lean
VTS/<module>/View.lean` (with `~/.elan/bin` on PATH) re-checks one file.
A failed obligation does not stop the check: everything else, also in the
modules that import the failing one, is still checked, so one run shows every
failure. An item that uses a failed one is `INCOMPLETE` even when its own
obligations are proved (they relied on the failed contract); fix the failure it
names first. A file marked `?` in the table has obligations that were not
checked (the reason is printed: it depends on a failure elsewhere — its goal,
or the proof Lean found, contains the `sorry` of a failed obligation or a
`hole()`; fix that first —, its declaration did not elaborate, or a Lean build
error stopped the file) — fix the first failure or the listed Lean build error
and re-run.
Each obligation has its own time budget; one that runs out fails with
`(deterministic) timeout` at that obligation (help the prover, or raise
`"heartbeats"` in vreact.json — default 1000000, at most 1000000000, 0 for no limit). After a timeout the report tries
each case of the goal alone (the branches of its `if`s and `switch`es, smallest first) and
names the case that fails, with that case's goal (or the first that did not finish); the short
report then shows only that goal. A case's name lists the branches that lead to it, outermost
first: `isTrue`/`isFalse` are the two branches of an `if` (a `switch` on a number or a string is
a chain of `if`s, one per group of labels sharing a body, in the order written, `default`'s own
labels too), `h_k` is the k-th alternative of a `match` (a `switch` on a
union or an enum has one per `case` label in the order written, then one for the rest:
`default`, wherever it is written). The lines of obligations that were not checked name each
one's position and kind (`src/OptionsChain.tsx:150:11 [callback]: it depends on …`).

Kinds → usual fix: see `reference/obligations.md` (handler, handler-robust,
handler-rebased, effect-robust, init-invariant, props-stability, unique-keys,
child-precondition, callback, callback-rebased, callback-contract, index,
nonzero-divisor, non-null, precondition,
postcondition, root-precondition, unreachable, assert).

## Helping the prover (only after the code and spec are right)

1. Strengthen what is known: a missing `invariant`, a stronger `ensures` on a
   helper, a `requires` on a child component. Facts about **constant data**
   (a seat map, a catalogue): mark the constant `/** @opaque */` and state the
   fact at module level, e.g. `assert(distinct(SEATS, (s) => s.id));` — it is
   proved once by evaluation (every `@opaque` constant it mentions unfolded)
   and supplied to every proof that mentions the constant (the first `@opaque`
   constant of the module it mentions). (Transparent constants are unfolded
   into every goal; large ones become long disjunctions that slow or defeat the
   prover.)
2. Split work: make a large function `@opaque` with precise `ensures`.
3. Add an intermediate fact: `assert(cond)` (proved, then available).
4. Write a Lean lemma in `proofs/<Module>.lean` (`import VTS.<Module>.Defs`;
   `<Module>` is the Lean module name: `src/Base.ts` is `Base_`, `src/base.ts` `base_`, `src/_util.ts`
   is `M_util`, see reference/obligations.md); tag it `@[vreact_simp]` if it is a rewrite rule (or `@[grind …]`). The lemma
   helps the module's component obligations, the `ensures` of the module's functions that no other
   function or constant of the module uses (they are proved after it, in
   `Posts.lean`), and everything (functions, contracts, components) in the
   modules that import `<Module>`. It does not help function bodies of
   `<Module>`, nor the `ensures` of a function that another function or
   constant of `<Module>` calls (those are proved in `Defs.lean`, before it,
   so the caller can use them). For such a lemma: state it generically in
   `proofs/Base.lean` (imported everywhere, so it imports no generated module), or move the function that needs
   it to a module that imports `<Module>`. Proof files may contain only lemmas
   (`theorem`/`def`/`abbrev`/`example`, `open`, `namespace`/`section`, the
   attributes `simp`/`vreact_simp`/`grind`, `grind_pattern`, resource options) and
   import only `VReact` (the whole library), `VTS.…`, `Proofs.…`:
   `vreact` rejects anything else — macros, `macro_rules`, instances, axioms,
   `VReact.assumed`, `#eval`, other options — before Lean runs, and re-checks what
   they added with Lean's kernel after the build. A proof file that no module
   imports (named after no module, e.g. `proofs/model.lean` for `src/Model.ts`, and
   imported by no such proof file) is rejected: Lean would never check it. So is a
   proof file whose path is not a module name (every directory and file name an
   identifier: not `proofs/x.y.lean` or `proofs/my-lemmas.lean`). See
   `reference/obligations.md`.
5. Never use `assume(…)` or `@trusted` to make a failure go away without telling
   the user; both are reported and keep the result from being `VERIFIED`.

## Reporting to the user

State the verdict line, counts, and what remains trusted/pending. Do not call a
result verified unless `vreact verify` said `✔ VERIFIED`.
