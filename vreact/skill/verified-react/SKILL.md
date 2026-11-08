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
`tool/docs/WALKTHROUGH.md`.

## Setup (once per machine / project)

```bash
bash <skill>/scripts/setup.sh                 # checks Node ≥ 22.6, Lean 4 (elan), builds the Lean library
bash <skill>/scripts/setup.sh /path/to/app    # also: npm i the tool into the app, write vreact.json
```

Installing Lean (elan, ~400 MB) changes the user's machine: ask first if it is
missing. All the app needs from npm is that `vreact` (and `react`, `@types/react`)
resolve from its folder — `npm i <tool>` or a symlinked `node_modules` both work. The app needs `"strict": true` and `"lib": ["ES2023", "DOM"]` in tsconfig and `vreact.json`
(`{"src":"src","exclude":["main.tsx"],"proofs":"proofs","out":".vreact"}`).
Keep `main.tsx` (createRoot) outside the verified program.

## The workflow

Work in small verified increments; run `vreact verify` after every meaningful
change (it is incremental and usually takes seconds).

1. **Model first.** Put state types, the invariant (a `boolean` function such as
   `wellFormed(b)`) and pure operations in a `.ts` module. Give operations
   contracts before bodies:
   * reducers and anything called from a functional update or `dispatch` must be
     **total** — no `requires`; state invariant preservation as
     `ensures((r: T) => implies(inv(s), inv(r)))`;
   * add **functional** postconditions (what the operation achieves), not only
     invariant preservation — otherwise `return s` satisfies the spec;
   * mark big operations `/** @opaque */` so callers reason by contract.
2. **Synthesize / implement.** Leave `return hole<T>();` and run
   `vreact synth src/model.ts --write`. If it returns a trivial program
   (`return s`), the spec is too weak — strengthen it. Synth builds
   *straight-line* expressions: field updates `{ ...s, f: e }` (one or two
   fields), record/variant literals, `[...xs, e]`, `[...xs, ...ys]`,
   `xs.filter(x => x.k !== v)`, `xs.map(x => x.k === v ? { ...x, f: e } : x)`,
   calls of the module's total helpers, `± 1` and comparisons — smallest first,
   up to size 9. Each hole costs up to ~60 s of search plus up to 5 Lean checks
   of candidates that pass the random tests; a function with n holes takes up
   to about n times that. Guarded updates (`if … return s;`)
   are not in the grammar: write the guard by hand and leave a hole in each
   branch (or `case`) — the holes of one function are filled and proved
   together (holes in different branches or cases are searched once each,
   whatever the others are filled with). `✔ proved by Lean` means Lean checked
   the whole function; `(relative to …)` — `"status": "proved-relative"` with
   `relative_to` under `--json` — means the proof assumes those @trusted
   contracts or `assume(…)` facts. A `? not proved` line names what kept Lean
   from checking it (often a failing obligation elsewhere in the module or an
   import: fix that first); a contract whose statement depends on a function
   that still has a hole (through calls, their bodies and `requires`; not
   through `@trusted` bodies) is reported as such: fill that function first. Synth never edits the
   file while searching; `--write` writes only proved fills.
3. **Reducer** — a total `switch` over a discriminated-union action type,
   delegating to the model; `ensures` that it preserves the invariant.
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

* Use `int` for integers (counts, ids, cents); `number` is a float the prover cannot reason about.
* State is immutable: spread, `filter`, `map`, `toSorted`, `with` — never `push`/`sort`/property assignment.
* Handlers may call setters, `dispatch`, and **at most one** parent callback per path.
* `setX(v)` uses the render snapshot; two of them in one handler do not compose — use
  `setX(prev => …)` when updates must accumulate.
* Effects/timers and continuous/default-priority handlers (`onMouseMove`,
  `onScroll`, `onTransitionEnd`, `onLoad`, …) must preserve the invariant from
  **any** state (stale closures): prefer functional updates there; effect deps
  must be exhaustive. Cleanups only clear timers (and log / write `localStorage` /
  `document.title`; the arguments of such writes are checked everywhere, like any
  expression). In such a component, clicks etc. must also be safe on top
  of their pending updates (React rebases): guard inside `setX(p => …)`.
* Closures read `let`s when they run: do not reassign a `let` after creating a
  handler/helper/updater that reads it (`const xNow = x;` first), and never assign
  an outer `let` inside a callback.
* Read event fields in the handler itself: `const v = e.target.value;
  setX((p) => … v …)` — a functional update runs after the event's dispatch
  (`e.currentTarget` is null then), so reading `e.…` inside it is rejected.
* Invariants must not depend on props that can change (React keeps state across
  prop changes): clamp when rendering instead.
* Lists need `key={…}` with provably distinct keys (usually from an invariant).
* One native event may reach only one discrete handler: no `onX` element may wrap
  a handler fired by the same native event (`onClick` around a checkbox's
  `onChange`: both run on click) or a user component, and one element may not
  combine such handlers (checkbox `onClick` + `onChange`; `onInput` + `onChange`).
  A click's activation counts too: no `onClick` on, around or inside a submit
  button of a form with `onSubmit` (use `type="button"`) or a `<label>`, and no
  `<label>` or nested button inside such a submit button.
  `onFocus`/`onBlur`/`onInvalid` must be robust (no parent callbacks).

## Reading results

`vreact verify` reports, per component/function (and per constant, when not
`VERIFIED`): `VERIFIED`, `VERIFIED*` (own obligations proved, relies on
`@trusted` contracts), `TRUSTED`, `ASSUMES` (relies on `assume(…)` facts),
`INCOMPLETE` (a failed or unchecked obligation, `hole()`/`sorry`, a declaration
Lean could not finish, or it relies on an item that is not verified — the line
under it names the reason, e.g. `↳ it uses clamp (src/lib.ts), which is not
verified: an obligation of it failed`), `UNCHECKED` (Lean never got to it: a
Lean build/import error or an internal error stopped its file), plus each failed obligation as
`file:line:col [kind] description` followed by the Lean goal. In the goal, the
hypotheses are what is known (props precondition, invariant, branch
conditions, `h_…` facts); `⊢ False` after `grind` means the facts were
insufficient — often a real counterexample is visible in them (e.g. `h : total = 0`).
Goals are abridged; `vreact verify --full` prints them completely (`--json`
has both `lean` and `leanFull`). `vreact explain <file>` prints the generated
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
`"heartbeats"` in vreact.json — default 1000000).

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
   proved once by evaluation and supplied to every proof that mentions the
   constant. (Transparent constants are unfolded into every goal; large ones
   become long disjunctions that slow or defeat the prover.)
2. Split work: make a large function `@opaque` with precise `ensures`.
3. Add an intermediate fact: `assert(cond)` (proved, then available).
4. Write a Lean lemma in `proofs/<Module>.lean` (`import VTS.<Module>.Defs`);
   tag it `@[vreact_simp]` if it is a rewrite rule. It helps the module's
   component obligations, the `ensures` of the module's functions that no other
   function or constant of the module uses (they are proved after it, in
   `Posts.lean`), and everything (functions, contracts, components) in the
   modules that import `<Module>`. It does not help function bodies of
   `<Module>`, nor the `ensures` of a function that another function or
   constant of `<Module>` calls (those are proved in `Defs.lean`, before it,
   so the caller can use them). For such a lemma: state it generically in
   `proofs/Base.lean` (imported everywhere), or move the function that needs
   it to a module that imports `<Module>`. See `reference/obligations.md`.
5. Never use `assume(…)` or `@trusted` to make a failure go away without telling
   the user; both are reported and keep the result from being `VERIFIED`.

## Reporting to the user

State the verdict line, counts, and what remains trusted/pending. Do not call a
result verified unless `vreact verify` said `✔ VERIFIED`.
