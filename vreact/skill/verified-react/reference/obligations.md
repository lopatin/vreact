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
| `unique-keys` | keys of a rendered list, or of the keyed children of one element or fragment (as strings: `key={1}` and `key="1"` collide), are distinct | add `distinct(...)` to the invariant or the child's `requires`; for the values of a Map, key by the Map key (`[...m].map(([k, v]) => <li key={k}>…)`) or add `[...m].every(([k, v]) => v.id === k)` to the invariant; for sibling elements, give each a key with its own literal prefix (`` key={`viewer-${id}`} ``, `` key={`notes-${id}`} ``) |
| `child-precondition` | props passed to `<C/>` satisfy `C`'s `requires` | establish it from your invariant / data; or weaken `C`'s requires |
| `callback` | the function you pass as a child's callback keeps **your** invariant, assuming the child's `callbackRequires` | strengthen the child's contract, or guard in your handler |
| `callback-contract` | this call of a callback prop satisfies its `callbackRequires` | the arguments you pass (e.g. trim/validate first) |
| `index` | `xs[i]` / `xs.with(i, …)` is in bounds | guard `i < xs.length` (in contracts too: `i < xs.length && xs[i] > 0`, `forall(0, xs.length, (i) => …)`), or carry bounds in an invariant |
| `nonzero-divisor` | `%`, `idiv`, `Math.floor(a/b)` divisor ≠ 0; a number division `a / b` (unless `b` is a nonzero literal): `b` not 0 (VTS values do not keep the sign of zero, which `1 / -0` would show) | guard (`total === 0 ? 0 : …`), `requires(b !== 0)` |
| `non-null` | `x!` is not null | narrow with `!== null` instead |
| `precondition` | a called function's `requires` holds; at a `dispatch(a)`, the reducer's `requires` about the action | establish it (validate before dispatching, or rely on a child's `callbackRequires`), or make the callee total |
| `postcondition` | a function's `ensures` holds | the body; or the ensures is false (too strong); a generic function's must hold for every instantiation (its type parameters are abstract in the goal) |
| `root-precondition` | the root component can be mounted | root `requires` must hold for its (empty) props |
| `unreachable` | a `throw` can never execute | guard; or prove the case impossible via invariant |
| `assert` | an `assert(c)` holds | — |
| `fact` | a module-level `assert(c)` about an `@opaque` constant holds | the data; it is checked by evaluation (it runs when the module loads: it, like a constant's initialiser, may not reach a constant declared below it, also through calls — rejected before any obligation). It is proved after every declaration it mentions (it may call a function declared below its constant); declarations before that point cannot use it |

`index`, `non-null`, `nonzero-divisor` and `precondition` come from every
expression JS evaluates, also where its value is not used: the arguments of
`console.*`, `localStorage.setItem` and `document.title = …` (in handlers,
effects, timers, render and functions), a timer's delay, and the conditions and
arguments of an effect's cleanup — checked where the effect returns it, under
the effect's early returns and branches. Guard them as usual (`if (i <
xs.length) console.log(xs[i].name)`). The same holds for the condition of
`requires`, `invariant`, `assert`, `assume` and a module-level `assert`, which JS
evaluates at every call, render or load: there `implies(a, b)` evaluates `b` even
when `a` is false, so `b`'s obligations get no help from `a` — write `!a || b`
(`xs.length === 0 || xs[0] > 0`). Only an `ensures` lambda and the expression
body of a `callbackRequires` lambda never run: there `b` is checked under `a`.

## When the code and spec are right but the proof fails

1. **Make the knowledge available.** The prover only knows: props `requires`,
   the `invariant`, branch conditions on the path, contracts of called
   `@opaque` functions (instantiated at each call, also under a binder: inside a timer
   callback, a functional update `setS((s) => …)`, a continuous or rebased handler, a
   `map`/`every` lambda; not at a call that occurs only inside a quantified hypothesis,
   e.g. an invariant `xs.every((x) => f(x) > 0)`, which the automation instantiates
   itself, without the contract: state what the proof needs about `f` in the quantified
   fact itself or as an `assert`), and definitions of transparent functions. A fact you
   "know" but never wrote down is missing — add it as an invariant, `requires`,
   or `ensures` (they are then proved once and reused everywhere).
2. **Go modular.** Big model functions: mark `/** @opaque */`, give precise
   `ensures` (one per property — they are proved and instantiated separately).
   Callers then reason only with the contracts (`vreact_contracts` instantiates
   them at each call), which is faster and more robust. A helper used at several
   types can be one generic `@opaque` function (`function removeKey<K extends int
   | string>(…)`, `function upsertById<T extends { readonly id: int }>(…)`): its
   body and contracts are proved once, for every type, and the contracts are
   instantiated at each call, whatever the type (also inside other generic
   functions).
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
   `VTS.<module>.<fn>` with contracts `<fn>.post`, `<fn>.post2`, … (a generic
   function's first binders are its type parameters `{T : Type}`, then
   `[DecidableEq K]` for equality constraints and one accessor `(T_id : T → Int)`
   per constrained field; its contracts have the same binders); components
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
   it comes after it. With such a file, the `ensures` theorems of the functions
   that no other function or constant of the module uses move to
   `VTS/<Module>/Posts.lean`, after the lemmas (the module's `View.lean` and the
   `Defs.lean` of the modules importing it import `Posts.lean`). So the lemmas
   help the component obligations in the module's own `View.lean`, those
   `ensures`, and **everything in the modules that import `<Module>`** (their
   `Defs.lean` imports `Proofs.<Module>`: function bodies, `ensures`, views).
   They cannot help `<Module>`'s own function bodies, nor the `ensures` of a
   function that another function or constant of `<Module>` uses (proved in
   `Defs.lean`, before the lemmas). So, for a lemma about a function `f` of
   module `A`:

   * needed by a function of module `B` that imports `A`, by `A`'s components,
     or by the `ensures` of a function of `A` that nothing else in `A` calls
     (`f` itself, say): put it in `proofs/A.lean`;
   * needed by a function body of `A`, or by the `ensures` of a function of
     `A` that another function of `A` calls: state it generically (about
     lists, integers, … — not about `VTS.A.f`) in `proofs/Base.lean`, which
     every `Defs.lean` imports; or move the function that needs it to a module
     that imports `A`; or help it with `assert(…)` and contracts of helper
     functions.

   A lemma in `proofs/A.lean` cannot use the `ensures` theorems that are in
   `Posts.lean` (they come after it); prove the fact from the definitions.

   (A `proofs/A.lean` that itself imports `VTS.B.…` of a module `B` importing
   `A` would form an import cycle; `B` then sees only `A`'s definitions.)

   **What a proof file may contain.** Proof files are imported by the generated
   Lean, so `vreact` checks each one before Lean runs (it parses it with Lean's
   parser) and rejects, with file:line and the command, anything but:
   * `import`s of `VTS.…` (generated modules), `Proofs.…` (other proof files),
     `VReact` (the whole library: not a part such as `VReact.JS`) and `Init` (or no
     import at all; not a part such as `Init.Core`) — the file is checked in the
     environment of its imports;
   * `theorem`, `def`, `abbrev`, `example` (with a doc comment, `private`,
     `protected`, `noncomputable`), named outside the namespaces `VTS` and
     `VReact` (those hold the generated declarations and the library: a lemma
     there could replace or extend a translated declaration) and not like a
     `VReact.` name;
   * `open`, `namespace`/`section`/`end` (not `VTS…`/`VReact…`; `noncomputable
     section` too), `variable`, `universe`, `include`, `omit`, `/-! … -/`,
     `#check`, `#print`, and `open … in` / `set_option … in` before one of these
     or a declaration (not before `namespace`/`section`/`end`);
   * the attributes `simp`, `vreact_simp`, `grind` (`grind =`, `grind →`, …), also
     `local` and erased (`attribute [-simp] f`), and `grind_pattern`: this is how
     the automation is extended (there is no `macro_rules` for `vreact_auto`);
   * `set_option` of `maxHeartbeats`, `maxRecDepth`, `synthInstance.maxHeartbeats`,
     `synthInstance.maxSize`, `autoImplicit`, `relaxedAutoImplicit`,
     `diagnostics`, the `linter.*` and `pp.*` options, and `trace.C` for a trace
     class `C` (`trace.Meta.Tactic.simp`, `trace.grind.ematch`, …; not
     `trace.profiler…`, which writes files or starts a web server) — also `… in`, in
     tactics and in grind's `grind => set_option … in …`;
   * any term or tactic except `run_tac`, `by_elab`, `unsafe`, `include_str`,
     `native_decide`/`+native`, `decide (config := …)` (write `decide +kernel` etc.),
     the `bv_decide` tactics, `Lean.ofReduceBool`, `dbg_trace`/`dbgTrace…` (they
     print to Lean's output) and `assumed`/`VReact.assumed` (the axiom behind the
     source's `assume(…)`: a lemma proved with it proves anything, and the report
     would blame `assume(…)` facts the source does not have), also through the
     tactic `vreact_assume` the translator writes for an `assume(…)`;
   * strings, characters and names on one line: no line breaks (or other control
     characters, also as escapes `\n`) in literals and `«…»` names — Lean prints them
     in messages, where a line could read like a message about a generated file.

   Rejected, with the reason: `axiom` (an unproved assumption: use `assume(…)` or
   `@trusted` in the source, which the report shows), `instance` and `deriving`
   (they change which `==`, `DecidableEq` or string conversion the generated code
   uses), `macro`, `macro_rules`, `syntax`, `notation`, `elab`, simprocs (they change
   how the generated code and the tactics parse and run), `#eval`, `run_cmd`,
   `initialize` (they run code), `opaque`, `structure`, `inductive`, `partial`,
   `export`, other attributes (`implemented_by`, `extern`, `reducible`, `instance`,
   …) and options (`debug.skipKernelTC`, …). A lemma admitted with `sorry` is
   accepted but shows as `sorryAx` in the axioms of everything that uses it
   (`INCOMPLETE`); an axiom of native evaluation (`…._native.…`,
   `Lean.ofReduceBool`) wherever it shows makes the result NOT VERIFIED.

   After the build, `vreact` re-checks every declaration of the generated modules
   and the proof files with Lean's kernel in a fresh process, and checks that each
   proof module added only theorems, definitions and simp/grind attributes (no
   syntax, macro, instance, alias, option, axiom, definition in `VTS…`/`VReact…`,
   nor a declaration using `VReact.assumed`). A proof module that fails this is an
   error of the user proofs, and no generated module importing it is `VERIFIED`:
   whatever was elaborated after it is not trusted. Lean's build files in
   `.vreact/.lake` are not evidence either: `vreact` removes a build directory it
   did not leave behind itself and builds everything again (so do not commit or
   share `.vreact/`; it is a cache).
5. **Large constants.** Transparent constants (`@[vreact_simp, reducible]` in
   the generated Lean) are unfolded into every goal that mentions them; a list
   literal of dozens of records turns into long disjunctions. Mark such constants
   `/** @opaque */` and state what proofs need as module-level `assert(...)` facts.
6. **Inspect.** The short report shows at most 18 lines of a goal: the conclusion and the
   hypotheses next to it (the one right above the conclusion whole when it fits), with
   contract instances, multi-line definitions and other long hypotheses (only as many as
   needed) each collapsed into one line that names and counts them, and the hypotheses
   farthest from the conclusion named by one line `… (k earlier hypotheses: …)` (see
   "Reading results" in SKILL.md).
   `vreact verify --full` prints complete goals; `vreact explain
   src/X.tsx` prints the generated Lean; the project in `.vreact/` can be opened
   in a Lean editor or re-checked file by file with `lake env lean <file>`; each
   obligation is `(/-⟦obN⟧-/ by vreact_ob vreact_auto)`.
7. **Timeouts.** Every obligation has its own heartbeat budget (`vreact_ob`,
   `"heartbeats"` in vreact.json, default 1000000). One that runs out fails
   *at that obligation* with `(deterministic) timeout`; the others are still
   checked. Make the goal smaller (`@opaque` helpers with `ensures`, `assert`)
   before raising the budget. After a timeout the report tries each case of the goal
   alone (smallest first, with a tenth of the budget each, half of it in all) and names
   the case that failed, with its goal, or the first that did not finish. A case's name
   lists its branches, outermost first: `isTrue`/`isFalse` are the branches of an `if`
   (also the bodies of a `switch` on a number or a string, a chain of `if`s), `h_k` the
   k-th alternative of a `match` (a `switch` on a union or an enum: one per `case` label
   in the order written, then `default`). The failing case is often a real
   counterexample: read its hypotheses. (`vreact_auto could not prove the goal (grind
   stopped at Lean's recursion limit)` is not a timeout: `grind` gave up on a
   hypothesis shape it cannot handle, and the other strategies did not prove
   the goal either. Guarded contracts `xs.length === 3 && forall(0, 3, i =>
   xs[i] >= 0)` are split and instantiated at the indices of the goal
   automatically; in a shape that is not, an `assert` of the needed instance
   usually helps.) A timeout or error Lean reports for a whole declaration
   leaves its obligations unproved ("not checked", with the reason). Budgets
   are per obligation also when Lean elaborates declarations in parallel; the
   one-time cost of a shared auxiliary lemma (equation lemmas of a big `match`)
   goes to whichever obligation needs it first (well under 1% in practice).
8. **What the automation knows about lists.** Distinct keys and counts follow
   chains of `filter`/`slice`/`toSorted`/`toReversed` from a list whose
   `distinct(...)` is a hypothesis (an invariant, a `requires`), also through
   `const`s and through a `map` that keeps the key (`xs.map(bump).slice(0, 3)`
   keyed by `id` when `bump` returns `{...r, age: …}`); deleting by the key of a
   present element of a list with distinct keys removes exactly one element, and
   a map-update by key (`xs.map(x => x.id === k ? {...x, done: !x.done} : x)`,
   also written with `!==` or as an `if` that returns `x` early) changes a
   `filter(...).length` by at most one. Facts about every (or some) element of a
   map-updated list are stated about the updated elements, so a reducer with
   many map-update arms stays within one obligation's budget. A disjunction over
   the cases of an enumeration or union (`(c === "red" && n === 1) || (c ===
   "green" && …)`, also on `o.inner.mode`) is proved by splitting the
   enumeration (up to three nested fallback levels). `%` with a non-negative
   dividend and a non-zero divisor is in `[0, |divisor|)`, and its exact value
   is known where index arithmetic needs it: `a % n === a` for `0 <= a < |n|`
   (and for `-|n| < a <= 0`), `n % n === 0`.
   Maps and Sets: `get`, `has` and `size` after `set`/`delete` (also through chains of them),
   distinct keys (`[...m.keys()]`, `[...m.entries()]` keyed by `k`; `[...m.values()]` keyed by
   `v.id` when an invariant says `[...m.entries()].every(([k, v]) => k === v.id)`), the position
   of a key after `set` (`[...r.keys()].indexOf(k)`: kept for a present key, last for a new one),
   every value after a `set` (`[...r.values()].every(…)`), that a value read with `m.get(k)` is
   the value of `k`'s entry (an invariant over `[...m.entries()]` applies to it), that every key
   and every value belongs to an entry (an invariant over `[...m]` applies to `m.has(k)` and to
   `[...m.values()]`; `[...m].some(([j]) => j === k)` is `m.has(k)`; merging two Maps keeps
   the keys of both), the entries and
   values of `new Map`/`new Set` of literals, of `new Map(pairs)` (also of a filtered `[...m]`)
   and of the loops `for (const x of xs) n.set(f(x), g(x))` / `n.add(f(x))` / `n.add(x)` (as `new Map`/`new
   Set` of the mapped list: every entry is one of the pairs), `[...m].length` and
   `[...m.values()].length` as `m.size` (so `[...m][0]` under `m.size > 0`), `new Set(xs).size
   <= xs.length` (`===` under `distinct(xs)`), `new Map(pairs).size === pairs.length` under
   distinct keys, and membership in a Set after `add`/`delete`, also of a Set stored in a Map
   (`r.get(k)!.has(x)`), that an index `new Map(xs.map((x) => [x.id, x]))` (or the loop
   `for (const x of xs) n.set(x.id, x)` from an empty Map) maps each `x.id` to `x` under
   `distinct(xs, (x) => x.id)`, and pigeonhole on distinct elements: when every member of `a`
   is in `b` (every key, for Maps), `a.size <= b.size`, and with `b.size <= a.size` every member
   of `b` is in `a` (`sameMembers` = equal sizes and one inclusion). All of this holds for
   abstract keys too (a generic helper over `ReadonlySet<K>` / `ReadonlyMap<K, V>` with
   `K extends int | string`: Lean `[DecidableEq K]`). Facts about other loops over Maps (a loop
   of `delete`s, a sum over `m.values()`, a count `n.set(x, (n.get(x) ?? 0) + 1)` that reads
   `n`) need a lemma, as for arrays; the model's lemmas (`JSMap.keys_set`,
   `JSMap.entries_set`, `JSMap.get_set`, `JSMap.mem_entries_of_get`, …) are in
   `VReact/JSMap.lean`.
9. **Bounded quantifiers.** `forall(lo, hi, i => …)` and guarded `&&` in
   hypotheses are split and instantiated at the indices of the goal, also
   nested (`g[r][c]` of a 2-D grid); to *establish* one with numeral bounds
   (an `init` of 9 cells, `cells.with(k, v)` under `forall(0, 9, i => cells[i]
   >= 0 && cells[i] <= 2)`), the goal is split into its conjuncts and, if
   needed, into one case per index (at most 16 values).
10. **Failures do not stop the check.** `vreact_ob` reports a failed obligation as
    a Lean *warning* (`vreact: …`, with the goal) and admits its goal with
    `sorry`, so the rest of the module and the modules importing it are still
    checked; a proved one reports `vreact:ok` (the report counts nothing as
    proved without it). Whatever relies on a failed obligation has `sorryAx` in
    its axioms and is `INCOMPLETE`, with the failed item named as the reason. An
    obligation that depends on such a `sorry` itself is reported
    `vreact:blocked …` and counted as *not checked*, neither proved nor failed:
    its goal contains it (an index obligation in its `ensures` or `requires`
    failed), the proof Lean found uses it (e.g. it unfolds a function whose
    index obligation failed: a proof through the admitted proof of a false
    statement proves nothing), or it failed on a goal that unfolds to a
    `hole()`. Fix the failure it depends on first. (Using the *contract* of a
    function whose `ensures` failed is ordinary modular reasoning: that
    obligation counts as proved, and its item is `INCOMPLETE`.)

## What not to do

* Do not add `assume(…)` or `@trusted` to silence a failure; they are reported
  (`ASSUMES` / `TRUSTED`, verdict "VERIFIED modulo assume(…) facts / @trusted
  declarations") and the app is then not verified. A lemma in `proofs/` cannot
  stand in for them: `VReact.assumed` (the axiom behind `assume(…)`), the tactic
  `vreact_assume` and `axiom` are rejected in proof files, and the kernel re-check
  breaks every module importing a proof module that uses an axiom.
* Do not weaken an `invariant` until it says nothing; check with `vreact synth`
  or by asking "what would a buggy implementation be allowed to do?".
* Do not "fix" a `props-stability` failure by removing the prop from the
  component's API without telling the user; it reflects real React behaviour.
