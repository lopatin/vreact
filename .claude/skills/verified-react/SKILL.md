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
`INCOMPLETE`, `TRUSTED`, `VERIFIED*`, `sorryAx`, `VReact.assumed` — is not done;
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
bash <skill>/scripts/setup.sh /path/to/app    # also: npm i the tool into the app, write vreact.json, Lean editor files
```

Installing Lean (elan, ~400 MB) changes the user's machine: ask first if it is
missing. All the app needs from npm is that `vreact` (and `react`, `@types/react`)
resolve from its folder — `npm i <tool>` or a symlinked `node_modules` both work. The app needs `"strict": true` in tsconfig and `vreact.json`
(`{"src":"src","exclude":["main.tsx"],"proofs":"proofs","out":".vreact"}`).
Keep `main.tsx` (createRoot) outside the verified program.

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
`.vreact/`). `lake build` in the app folder builds nothing (the app's package has no targets).
vreact keeps its own `lakefile.toml` (first line `# vreact: Lean editor support`) and
`lean-toolchain` up to date, and never writes either over a `lakefile.toml` without that line
or a `lakefile.lean` (the user's own Lean project).

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
   calls of the module's total helpers, `± 1` and comparisons — smallest first,
   up to size 9. Each hole costs up to ~60 s of search plus a Lean check per
   candidate that passes the random tests. Guarded updates (`if … return s;`)
   are not in the grammar: write them by hand.
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

* Use `int` for integers (counts, ids, cents); `number` is a float the prover cannot reason about.
* State is immutable: spread, `filter`, `map`, `toSorted`, `with` — never `push`/`sort`/property assignment.
* Handlers may call setters, `dispatch`, and **at most one** parent callback per path.
* `setX(v)` uses the render snapshot; two of them in one handler do not compose — use
  `setX(prev => …)` when updates must accumulate.
* Effects/timers must preserve the invariant from **any** state (stale closures):
  prefer functional updates there; effect deps must be exhaustive.
* Invariants must not depend on props that can change (React keeps state across
  prop changes): clamp when rendering instead.
* Lists need `key={…}` with provably distinct keys (usually from an invariant).
* No `onX` element may wrap another `onX` element or a user component (bubbling).

## Reading results

`vreact verify` reports, per component/function: `VERIFIED`, `VERIFIED*`
(own obligations proved, relies on `@trusted` contracts), `TRUSTED`,
`INCOMPLETE` (failed obligation or `hole()`), plus each failed obligation as
`file:line:col [kind] description` followed by the Lean goal. In the goal, the
hypotheses are what is known (props precondition, invariant, branch
conditions, `h_…` facts); `⊢ False` after `grind` means the facts were
insufficient — often a real counterexample is visible in them (e.g. `h : total = 0`).
Goals are abridged; `vreact verify --full` prints them completely (`--json`
has both `lean` and `leanFull`). `vreact explain <file>` prints the generated
Lean; `.vreact/` is an ordinary Lake project, so `cd .vreact && lake env lean
VTS/<module>/View.lean` (with `~/.elan/bin` on PATH) re-checks one file.
A file marked `?` in the table was not checked because a module it depends on
failed — fix the first failure and re-run.

Kinds → usual fix: see `reference/obligations.md` (handler, handler-robust,
effect-robust, init-invariant, props-stability, unique-keys, child-precondition,
callback, callback-contract, index, nonzero-divisor, non-null, precondition,
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
   tag it `@[vreact_simp]` if it is a rewrite rule. See `reference/obligations.md`.
5. Never use `assume(…)` or `@trusted` to make a failure go away without telling
   the user; both are reported and keep the result from being `VERIFIED`.

## Reporting to the user

State the verdict line, counts, and what remains trusted/pending. Do not call a
result verified unless `vreact verify` said `✔ VERIFIED`.
