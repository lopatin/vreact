# vreact — formally verified React, checked by Lean 4

`vreact` verifies React components written in **VTS**, a subset of TypeScript +
TSX with contracts. It gives every component a meaning in Lean 4, using a
semantic model of React's state queue, batching, snapshots and stale closures,
rendering, effects and reconciliation. Every safety property becomes a proof
obligation that Lean's kernel checks. It also **synthesizes** code for
`hole<T>()` placeholders against their contracts.

```
src/*.tsx ─▶ vreact verify ─▶ .vreact/ (Lean 4 project) ─▶ lake build ─▶ report + whole-app certificate
           ▲                                                                │
           └────────── fix code / spec, add lemmas ◀─────────────────────────┘
```

The same `.tsx` runs unchanged with Vite and React 18: contracts are no-op calls at runtime.

## What you get

For every component, proved:

* the state invariant holds initially and after **every** event handler
  (discrete events from the render snapshot; continuous events, effects and
  timers from *any* state, which rules out stale-closure bugs);
* the invariant survives prop changes (React keeps state across re-renders);
* rendering never fails (indices, divisions, `!`, callee preconditions);
* list keys are distinct;
* child preconditions hold, and parent/child **callback contracts** hold in both directions;
* plus static checks: hooks rules, exhaustive effect deps, no setState in render,
  immutability, no event-bubbling double handling.

For every function: its `ensures`. For every app root: `App.certificate`, an
instance of the theorem `VReact.run_allInv` ("in every run, every mounted
instance satisfies its invariant"), whose `#print axioms` lists everything the
app relies on.

## Commands

```bash
vreact verify   [--root DIR] [--json]     # translate, check every obligation, report
vreact synth    <file.ts[x]> [--write]    # fill hole<T>() placeholders (enumerate → test → prove)
vreact explain  [file.tsx]                # print the generated Lean
vreact translate                          # only generate .vreact/
```

## Layout

| path | what |
|------|------|
| `src/` | the translator (TypeScript compiler API → Lean), CLI, synthesizer |
| `spec/` | `vreact/spec`: `requires ensures invariant callbackRequires assert assume forall exists distinct implies idiv range hole` and `type int` |
| `lean/VReact/JS.lean` | exact model of the JS operations VTS allows (UTF-16 strings, `slice`, `%`, …) |
| `lean/VReact/Core.lean` | the React model: update queues, outcomes, proof-carrying `VNode`, `Spec`, `Component` |
| `lean/VReact/Runtime.lean` | lifecycle semantics (mount, reconcile, dispatch, effects, timers) and `run_allInv` |
| `lean/VReact/Tactic.lean`, `Contracts.lean`, `Lists.lean`, `Simprocs.lean` | `vreact_auto`: simp normalisation + per-call contract instantiation + `grind` |
| `docs/SEMANTICS.md` | the formal model, obligations, soundness theorem, trusted base |
| `skill/verified-react/` | the Claude Code skill (SKILL.md, references, setup script) |
| `tests/` | regression suite (`run.ts`: 23 semantic/rejection cases), synthesis test, sample apps |

## Requirements

Node ≥ 22.6 (runs TypeScript directly) and Lean 4 via elan (the version is pinned
in `lean/lean-toolchain`). Run `skill/verified-react/scripts/setup.sh [app]`.

## Tests

```bash
node --experimental-strip-types tests/run.ts          # 23 cases: React-semantics bugs caught, subset rejections
node --experimental-strip-types tests/synth.test.ts   # synthesis (append / remove-by-key / update-by-key, joint holes, what counts as proved)
(cd tests/todo && node ../../bin/vreact.js verify)    # small verified app with child callbacks
(cd ../examples/kanban && node ../vreact/bin/vreact.js verify)   # the walkthrough app: 79 obligations
```
