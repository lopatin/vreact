# Proof obligations: what each one means and how to fix it

Every failed obligation is reported as `file:line:col [kind] description`
followed by the Lean goal. Hypotheses above `⊢` are what is known; with
`grind`, `⊢ False` means the known facts did not suffice, and the remaining
hypotheses often *are* a counterexample. When an invariant is a conjunction and
the whole fails, the conjuncts are proved separately and the report shows the
first one that fails.

| kind | the claim | first thing to check |
|------|-----------|----------------------|
| `handler` | this discrete handler, run on the render snapshot, keeps the component invariant | guards before updates; two `setX(v)` from one snapshot do not compose (use `setX(p => …)`); update all fields the invariant relates |
| `handler-robust` | a continuous- or default-priority-event handler (`onMouseMove`, `onScroll`, `onTransitionEnd`, `onLoad`, …), or `onFocus`/`onBlur`/`onInvalid` (the DOM fires them inside other batches), keeps the invariant from **any** valid state | use functional updates; avoid relying on render values |
| `handler-rebased` | in a component with effects/timers/continuous handlers that set state, a discrete handler keeps the invariant also when React re-applies it on top of their pending updates (fields they write may differ from the snapshot) | guard inside the functional update (`setR(p => p.lo < p.hi ? … : p)`) instead of on the snapshot |
| `callback-rebased` | the same for a callback you pass to a child, in such a component | as for `handler-rebased` |
| `effect-robust` | an effect / timer callback keeps the invariant from any valid state (stale closure); a timer callback may use the early returns (`if (c) return;`) and `assert`/`assume` before its top-level registration | functional update over the whole related state (one record); an early return on the captured value before `setTimeout` |
| `init-invariant` | initial state satisfies the invariant | initial values; literal data in `useState(...)` |
| `props-stability` | the invariant survives a re-render with new props (React keeps state) | do not tie state invariants to changeable props; clamp in render |
| `unique-keys` | keys of a rendered list are distinct | add `distinct(...)` to the invariant or the child's `requires` |
| `child-precondition` | props passed to `<C/>` satisfy `C`'s `requires` | establish it from your invariant / data; or weaken `C`'s requires |
| `callback` | the function you pass as a child's callback keeps **your** invariant, assuming the child's `callbackRequires` | strengthen the child's contract, or guard in your handler |
| `callback-contract` | this call of a callback prop satisfies its `callbackRequires` | the arguments you pass (e.g. trim/validate first) |
| `index` | `xs[i]` / `xs.with(i, …)` is in bounds | guard `i < xs.length` (in contracts too: `i < xs.length && xs[i] > 0`, `forall(0, xs.length, (i) => …)`), or carry bounds in an invariant |
| `nonzero-divisor` | `%`, `idiv`, `Math.floor(a/b)` divisor ≠ 0 | guard (`total === 0 ? 0 : …`) |
| `non-null` | `x!` is not null | narrow with `!== null` instead |
| `precondition` | a called function's `requires` holds | establish it, or make the callee total |
| `postcondition` | a function's `ensures` holds | the body; or the ensures is false (too strong) |
| `root-precondition` | the root component can be mounted | root `requires` must hold for its (empty) props |
| `unreachable` | a `throw` can never execute | guard; or prove the case impossible via invariant |
| `assert` | an `assert(c)` holds | — |
| `fact` | a module-level `assert(c)` about an `@opaque` constant holds | the data; it is checked by evaluation |

## When the code and spec are right but the proof fails

1. **Make the knowledge available.** The prover only knows: props `requires`,
   the `invariant`, branch conditions on the path, contracts of called
   `@opaque` functions, and definitions of transparent functions. A fact you
   "know" but never wrote down is missing — add it as an invariant, `requires`,
   or `ensures` (they are then proved once and reused everywhere).
2. **Go modular.** Big model functions: mark `/** @opaque */`, give precise
   `ensures` (one per property — they are proved and instantiated separately).
   Callers then reason only with the contracts (`vreact_contracts` instantiates
   them at each call), which is faster and more robust.
3. **Intermediate facts.** `assert(c)` inside a function or handler proves `c`
   and adds it to what follows: the later obligations of the body and, in a
   handler, effect, timer or callback passed to a child, also its invariant,
   robustness and emit obligations. (Not a function's `ensures`: they are proved
   about its result, outside the body.)
4. **Lean lemmas.** `proofs/<Module>.lean` (path mirrors the module under `src`):

   ```lean
   import VTS.model.Defs
   open VReact

   -- a rewrite rule the automation will use in this module's views and
   -- everywhere in the modules that import it
   @[vreact_simp] theorem allCards_len (b : VTS.model.Board) :
       (VTS.model.allCards b).length = b.todo.length + b.doing.length + b.done.length := by
     simp [VTS.model.allCards]; omega
   ```

   Generated names: types `VTS.<module>.<Type>`, functions
   `VTS.<module>.<fn>` with contracts `<fn>.post`, `<fn>.post2`, …; components
   `VTS.<module>.<Comp>.{Props, Cb, State, pre, inv, render}`. A name that is a
   Lean keyword or root-level Lean name gets a `'` (`function max` is
   `VTS.<module>.max'`, field `rec` is `rec'`, component `Type` is
   `VTS.<module>.Type'`; a module path segment gets a `_`: `src/end/Sort.tsx` is
   `VTS.end_.Sort_`, its lemmas `proofs/end_/Sort_.lean`); hypotheses the translator invents
   are subscripted (`h₁`, `hmem₂`); all `requires` of a function form one
   hypothesis `h_pre`. Run
   `vreact explain src/<file>.tsx` to see them. `proofs/Base.lean` (no imports of
   generated code) is visible to every module.

   `Defs.lean` holds types, constants and functions, each function followed by
   its `ensures` theorems (so later function bodies, here and in importing
   modules, can use them). `proofs/<Module>.lean` imports that `Defs.lean`, so
   it comes after it: it helps the component obligations in the module's own
   `View.lean` and **everything in the modules that import `<Module>`** (their
   `Defs.lean` imports `Proofs.<Module>`: function bodies, `ensures`, views).
   It cannot help `<Module>`'s own function bodies and contracts. So, for a
   lemma about a function `f` of module `A`:

   * needed by a function of module `B` that imports `A`, or by `A`'s
     components: put it in `proofs/A.lean`;
   * needed by `f`'s own `ensures`, or by another function of `A`: state it
     generically (about lists, integers, … — not about `VTS.A.f`) in
     `proofs/Base.lean`, which every `Defs.lean` imports; or move the function
     that needs it to a module that imports `A`; or help it with `assert(…)`
     and contracts of helper functions.

   (A `proofs/A.lean` that itself imports `VTS.B.…` of a module `B` importing
   `A` would form an import cycle; `B` then sees only `A`'s definitions.)
   Declare lemmas outside the generated names: a user declaration named like a
   generated one (`VTS.A.f`, `VTS.A.f.post`) keeps the generated one out of
   Lean, and then `f` and everything that uses it is `INCOMPLETE`.
5. **Large constants.** Transparent constants (`@[vreact_simp, reducible]` in
   the generated Lean) are unfolded into every goal that mentions them; a list
   literal of dozens of records turns into long disjunctions. Mark such constants
   `/** @opaque */` and state what proofs need as module-level `assert(...)` facts.
6. **Inspect.** `vreact verify --full` prints complete goals; `vreact explain
   src/X.tsx` prints the generated Lean; the project in `.vreact/` can be opened
   in a Lean editor or re-checked file by file with `lake env lean <file>`; each
   obligation is `(/-⟦obN⟧-/ by vreact_ob vreact_auto)`.
7. **Timeouts.** Every obligation has its own heartbeat budget (`vreact_ob`,
   `"heartbeats"` in vreact.json, default 1000000). One that runs out fails
   *at that obligation* with `(deterministic) timeout`; the others are still
   checked. Make the goal smaller (`@opaque` helpers with `ensures`, `assert`)
   before raising the budget. (`vreact_auto could not prove the goal (grind
   stopped at Lean's recursion limit)` is not a timeout: `grind` gave up on a
   hypothesis shape it cannot handle, e.g. `forall(0, 3, …)` with a literal
   bound, and the other strategies did not prove the goal either; an `assert`
   of the needed instance, or a variable bound, usually helps.) A timeout or
   error Lean reports for a whole declaration leaves its obligations unproved
   ("not checked", with the reason).

## What not to do

* Do not add `assume(…)` or `@trusted` to silence a failure; they are reported
  (`ASSUMES` / `TRUSTED`, verdict "VERIFIED modulo assume(…) facts / @trusted
  declarations") and the app is then not verified.
* Do not weaken an `invariant` until it says nothing; check with `vreact synth`
  or by asking "what would a buggy implementation be allowed to do?".
* Do not "fix" a `props-stability` failure by removing the prop from the
  component's API without telling the user; it reflects real React behaviour.
