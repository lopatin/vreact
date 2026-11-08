# The vreact semantic model

What does "formally verified" mean for a React app built with vreact? This
document gives the precise answer: the language subset (VTS), its meaning in
Lean 4, the model of React, the proof obligations, the soundness theorem, and
the trusted base.

```
 .tsx (VTS)  ──vreact translate──▶  Lean 4 definitions + proof obligations  ──Lean kernel──▶  ✔ / ✗
   │                                     │
   │ tsc + Vite (unchanged code)         └─ VReact library: JS runtime model, React model,
   ▼                                        runtime semantics + soundness theorem, tactics
 browser
```

The `.tsx` you run is the `.tsx` you verify: vreact never generates the
JavaScript. It *reads* your code and gives it a meaning in Lean.

---

## 1. VTS — Verified TypeScript

VTS is a subset of TypeScript chosen so that every accepted construct has an
exact, total meaning in Lean, while still covering what real React code uses.

### 1.1 Types

| TypeScript                                   | Lean                                    | notes |
|----------------------------------------------|-----------------------------------------|-------|
| `boolean`                                    | `Bool`                                  | |
| `int` (alias of `number` from `vreact/spec`) | `Int`                                   | mathematical integers (2^53 not modelled) |
| `number`                                     | `JS.Num` (opaque type)                  | IEEE-754 doubles; every operation opaque: proofs know nothing about numbers |
| `string`                                     | `JS.Str` = list of UTF-16 code units    | **exact** JS strings (emoji, lone surrogates) |
| `"a" \| "b"`                                 | `inductive` enum                        | |
| `{ readonly f: T }`, `interface`             | `structure`                             | |
| `{kind:"a",…} \| {kind:"b",…}`               | `inductive`, one constructor per variant | discriminated unions |
| `readonly T[]`, `T[]`                        | `List T`                                | immutable |
| `T \| null`, `T \| undefined`, `f?: T`       | `Option T`                              | not both null and undefined |
| `[A, B]`                                     | `A × B`                                 | |
| `(x: A) => void` (props only)                | callback with a contract                | see §2.4 |

`T | null` and `T | undefined` share the Lean type `Option T`; which nullish
value a `none` stands for is taken from the TypeScript type of the expression
(optional fields, `find()`, `at()` and `?.` give `undefined`). A strict test
against the other nullish value (`t.due === null` with `due?: int`), a strict
test of a value that may be either (or whose type is `any`/`unknown`), and `===`
between a `T | null` and a `T | undefined` value are rejected: `== null` covers
both. This needs `strictNullChecks` and `noImplicitAny` (both part of `strict`;
rejected without them).

The parameters of function values are typed from the values they receive: the
declared return type for `ensures((r) => …)`, the callback prop's parameter types
for `callbackRequires` and for handlers passed to a child, the state type for a
functional update, the element (and `int` index) type for array-method callbacks
and quantifiers. TypeScript does not check an annotation there against that type
(`ensures` takes `any`; a callback annotation only has to accept the argument, so
`unknown` or `int | null` for an `int | undefined` argument pass), so an annotation
must be exactly that type — the same VTS type and the same nullish value at each
optional position (`number` may annotate an `int`: TypeScript does not tell them
apart) — or is rejected; default values, `?` and rest parameters are
rejected. An unannotated `ensures` parameter is TypeScript `any`, and so is what
is computed from it (`r.v`, `r[0]`): where such a value with an optional part goes
to a place whose TypeScript type tells null from undefined (an argument, an
element, a field, an initializer), its nullish value (from the declared return
type) must be the one that type says, or it is rejected (`isNull(r)` with
`isNull(x: int | null)` on an `int | undefined` result): annotate `r`, and
TypeScript checks it. Inline object types and string-literal unions are structural: the same
inline type in one module is one Lean type (`hole<{ readonly v: int }>()` in a
function returning `{ readonly v: int }`). A value is widened where TypeScript
allows it: an `int` to a `number`, a present value to an optional one, an array
elementwise (`int[]` to `(int | null)[]`), an enum member to its string.

Rejected: `any`, `as` casts, classes, `this`, mutation of objects/arrays,
`==` (except `== null`), `===` on objects (reference identity), generics,
exceptions (`try`), `var`, `while`, recursion (for now), recursive types,
`async`.

### 1.2 Expressions and statements — semantics by translation

Every expression maps to a Lean term whose value is the JavaScript value.

* Every emitted literal and local is type-ascribed (`(5 : Int)`, `let x : Int := …`,
  `(none : Option Int)`, `([…] : List Int)`), so Lean never infers a type the
  translator did not choose (a bare numeral would default to `Nat`).
* Arithmetic on `int` is integer arithmetic; `%` is ECMAScript's remainder
  (sign of the dividend), `Math.floor(a / b)` / `idiv(a, b)` is floor division —
  both carry the obligation `b ≠ 0`.
* `xs[i]` carries the obligation `0 ≤ i < xs.length` (JS would return `undefined`).
* Array methods `map filter some every find findIndex includes indexOf slice
  concat join reduce toSorted toReversed with at flatMap` and spread `[...xs, x]`
  map to their exact list counterparts (`slice` implements JS's negative-index
  clamping, `with` carries a bounds obligation). `toSorted(cmp)` follows
  ECMA-262: for a comparator that is *consistent* on the elements (`JS.Consistent`:
  reflexive, symmetric and transitive `=`, transitive `<` and `>`) the result is the
  unique stable sort; otherwise the order is implementation-defined (V8 and a
  merge sort differ, e.g. for `(a, b) => a.k < b.k ? -1 : 1` on ties), and the model
  only knows that the result is a permutation of the input (`JS.unspecifiedSort`, an
  unspecified function of the list and the comparator). `toSorted` on an array that
  may contain `undefined` is rejected (JS moves `undefined` to the end without
  calling the comparator).
  Every modelled method and `Math.*`/spec helper has an exact arity: optional
  arguments that are not modelled (`thisArg`, `fromIndex`, string positions) are
  rejected, never ignored. `includes`, `indexOf` and key-less `distinct` compare
  with Lean equality, which is JS's SameValueZero/`===` only for primitive
  elements (`boolean`, `int`, `string`, enums, options of these); on objects
  (identity) and `number` (NaN) they are rejected.
* String methods `trim includes startsWith endsWith slice repeat length` are
  exact on UTF-16 code units; `toLowerCase/toUpperCase` are opaque (Unicode case
  mapping is not modelled: proofs cannot depend on them). A literal is its cooked
  UTF-16 value; one with a lone surrogate (not a Lean `String`) is emitted as its
  code units `JS.Str.mk […]`.
* Numbers are the opaque type `JS.Num`, not Lean's `Float` (which the kernel
  computes with — Lean has a model of it — and whose library is not JavaScript's:
  `max 1 NaN = 1` while `Math.max(1, NaN)` is NaN, `Float.round` rounds half-way
  cases away from zero while `Math.round` rounds them up). Literals
  (`JS.Num.ofScientific`, `JS.Num.ofInt`), an `int` used as a number
  (`JS.Num.ofInt`), `+ - * /`, unary `-`, `<`, `<=`, `===`, `Math.floor/ceil/round/
  trunc/abs/max/min` and `String(x)` are opaque constants (`opaque` definitions, no
  axioms), so no proof can compute or decide anything about numbers: what is
  provable about them follows from hypotheses and congruence alone (`a / b < 0.5`
  is `a / b < 0.5`). In particular `===` on `number` is the uninterpreted IEEE test
  `JS.Num.eq` (not reflexive: `NaN !== NaN`), in code and in contracts alike, and
  nothing relates `JS.Num.lt`, `JS.Num.le` and `JS.Num.eq`. Unary `+` is only
  accepted on numbers (the identity). An integer literal used as a number is
  `JS.Num.ofInt n`, as an int used as a number is.
* **The sign of zero.** VTS values are JS values *up to the sign of zero*: an
  `int` that is 0 may be `-0` in JS (`-x`, `a * b`, `a % b`, `Math.trunc(a / b)`,
  `Math.floor(0 / -5)`, `idiv`, `Math.min(0, -0)`, the literal `-0`), Lean's `Int`
  has one zero, and `JS.Num.ofInt` maps it to one number (`JS.Num` stands for the
  doubles with `0` and `-0` identified). Every accepted operation gives equal
  results, up to the sign of zero, for `0` and `-0` — `===` and the comparisons
  (`-0 === 0`), `+ - *`, unary `-`, `%`, `Math.*`, `String(x)` and template literals
  (`"0"`), indexing and `slice`/`at`/`with` (ToIntegerOrInfinity), `includes`,
  `distinct` (SameValueZero), keys — except a division *by* a zero: `1 / 0` is
  `Infinity`, `1 / -0` is `-Infinity`. So `a / b` carries the obligation that the
  divisor is not zero (`JS.Num.divInt a b (h : b ≠ 0)` for an int divisor,
  `JS.Num.divNum a b (h : JS.Num.eq b (JS.Num.ofInt 0) = false)`, i.e. `b !== 0`, for a number),
  unless the divisor is a nonzero numeric literal (possibly negated, or a `const`
  initialised with one), in code and contracts alike. (Before, `1 / -x > 0` and
  `1 / x > 0` were one Lean term for `x = 0`, and an ensures comparing them was
  VERIFIED although false in JS: `RlNegZero.ts`.) React compares state and effect
  dependencies with `Object.is`, which tells `-0` from `0`; that decides only
  whether a component re-renders (with equal output) and whether an effect runs
  again, and effects are robust (§2.6), so it does not change what is verified.
* `a + b` with a string operand (by its TypeScript type) is concatenation; an
  `int`, `boolean` or enum operand is converted exactly as in a template literal
  (`-5 + "a"` is `"-5a"`); a `number` or possibly-null operand is rejected.
  Bitwise operators (`~ & | ^ << >> >>>`, also as `&=` …) are rejected (ToInt32 is
  not modelled), as are compound assignments other than `+=` and `-=`.
* `x!` carries the obligation `x ≠ null`; `?.` and `??` map to `Option.map/getD`.
* Narrowing (`x !== null`, `x.kind === "add"`, `switch (x.kind)`, early
  `return`) is compiled to Lean `match`, so the narrowed facts are available to
  every obligation in the branch. The complement of a tag test is narrowed too
  when it leaves one variant (else branch, code after an early return, the right
  of `||`, a ternary's false branch); with more variants left, the complement is
  split into one arm per variant only when later code needs it (a later test
  excludes all but one, or a field the remaining variants share). A variant
  narrowing of a `T | null` path (tested non-null first) also makes it present.
  Assigning a present value to an optional `let`
  narrows it as well; any later assignment (also in a `for…of`) drops what was
  known. A null test, `??`, `?.` or `!` on a value known to be present is decided
  statically (the value is not null); the operand is still evaluated, so its own
  obligations (`xs[5] === null`: the index; `g(x) != null`: g's precondition;
  `x! === null`: non-null) remain.
* Names: a VTS identifier that is a Lean token, a root-level Lean name the
  generated code may use unqualified (`max`, `some`, `List`, …) or a fixed name of
  the generated code (`σ`, `props`, `h_pre`, …) is primed (`max'`; fields and
  constructors also avoid `rec`, `mk`, `casesOn`, `rec_1`, …). A name shaped like
  the instances Lean declares for the module's types (`instReprP`,
  `instDecidableEqP`, `instToJSK`, `instToJSList'` for a type `List`: any `inst`
  followed by a capital) gets `''` (an instance name ends in at most one `'`), and
  a declared type of that shape is rejected (its instances could be another
  type's). A name starting with `_` is «quoted» with the `_` written `\u005f`
  (Lean reads `_hyg`, `_cstage1`, … specially). Names the
  translator invents are subscripted (`h₁`, `idx₀`). Neither `'` nor subscript
  digits can occur in a TypeScript identifier, so generated names and user names
  never capture each other. The lists are generated from Lean by
  `lean/scripts/GenNames.lean`. Enum members and discriminants are any strings:
  an ASCII identifier is used as is (primed if Lean generates that name in the
  type's namespace), anything else is «quoted» with `\`, `'`, `«`, `»`, control
  characters and lone surrogates written `\uXXXX` — injective, and the source stays
  UTF-8; union accessors are primed (`A.kind'`), so no constructor can clash.
  Component names follow the same rule (`function Type()` is the namespace
  `Type'`); a module path segment that would clash gets a `_` suffix instead, as
  it is also a directory name (`src/end/Sort.tsx` is the module `VTS.end_.Sort_`,
  its user lemmas go in `proofs/end_/Sort_.lean`).
* Statements are translated in continuation-passing style: `const` ↦ `let`,
  reassignment of a local `let` ↦ shadowing `let`, `if` ↦ dependent `if` (the
  condition becomes a hypothesis), `for (const x of xs)` ↦ `List.foldl` over
  the tuple of assigned locals (no `return`/`continue`, and a `break` only to end
  a `switch` case), `switch` ↦ `match` / if-chain (first matching
  label; `default` in any position takes the values no label matches; labels of
  a switch on an int, string, boolean or number are compared with `===`, and may be
  literals, negated literals or constants — a non-integer label on an int is
  rejected, it can never match), `throw`
  ↦ an obligation that the point is unreachable.
* A JSX const (`const row = <p>{e}</p>;`) is translated where it is declared —
  JS evaluates the element's attributes and `{…}` children there, whether or not
  (and wherever) it is rendered — so its obligations are checked at the
  declaration, under the facts that hold there; uses refer to that value (the
  event-bubbling checks of §2.4 still apply at each use). JSX elsewhere than in a
  component's render (functions, handlers, loops) is rejected.
* Functions created in a body (helper arrows, handlers, callback props,
  functional updates, effects, timers, cleanups, `useCallback`) are translated in
  the environment of the point where they are created. JS closures capture
  *variables*, so this is exact only under two static checks: a function that
  runs later may not read a `let` that may be reassigned after the function is
  created (a later assignment, or one in an enclosing loop), and no function —
  including immediately-run array callbacks — may assign a `let` declared
  outside it. Array-method callbacks, spec predicates and the `useMemo` factory
  run in place and read the current values.

### 1.3 Contracts (`vreact/spec`)

| construct                         | meaning |
|-----------------------------------|---------|
| `requires(c)` in a function       | hypothesis parameter `(h_pre : c)`; every call site must prove it (several `requires` are conjoined in order into one `h_pre`) |
| `ensures((r: T) => c)`            | theorem `f.post : ∀ args, h_pre → c[r := f args]` |
| `requires(c)` in a component      | the props precondition `pre`; every `<C …/>` must prove it (several are conjoined in order, as in functions) |
| `invariant(c)` in a component     | the state invariant `inv` (after the hooks; several are conjoined in order) |
| `callbackRequires(cb, (…) => c)`  | the contract of a callback prop (§2.4) |
| `assert(c)` / `assume(c)`         | obligation + fact / trusted fact (reported) |
| `forall exists distinct implies`  | bounded quantifiers, key uniqueness (`List.Nodup`), implication |
| `/** @opaque */` on a function    | callers see only its `ensures` (modular verification) |
| `/** @trusted */`                 | body not verified; contract assumed (reported, appears as a Lean axiom) |
| `hole<T>()`                       | a placeholder for `vreact synth`: `sorry`; while a function has one, its `ensures` theorems are `sorry` too (reported INCOMPLETE) |

A contract is a proposition with JS's evaluation order: the right operand of
`a && b` is translated under the hypothesis `a` (`∃ (h : a), b` when `b` has
proof obligations, plain `a ∧ b` otherwise), `a || b` as `a ∨ ∃ (h : ¬a), b`,
`c ? x : y` as `(∀ (h : c), x) ∧ (∀ (h : ¬c), y)`, `implies(a, b)` as
`∀ (h : a), b`, `forall(lo, hi, i => p)` as `∀ i, ∀ (h₁ : lo ≤ i), ∀ (h₂ : i < hi), p`
and `xs.every(x => p)` as `∀ x, ∀ (h : x ∈ xs), p`, so an index obligation in `b`,
`p`, … sees its guard. (In code, `implies` is a function call: both arguments are
evaluated.) Several `requires` (or `invariant`) statements are one condition
`c₁ && c₂ && …`: a later one may rely on the earlier ones as guards.
Narrowing tests in a guard narrow what JS evaluates under it, as in code — also
in a compound guard: in `b || s.kind === "a" || s.to.length > 0` (left-associated,
any length), `x !== null && y !== null && x + y > 0`, `!(x === null || y === null) || …`,
`implies(x !== null && …, …)` and `c ? … : …` the later operand is translated where
every earlier operand failed (held), each test becoming a `match`. Such a compound
guard is decomposed only when a later operand needs its narrowing; otherwise it
stays one condition (the normal forms above).

`assert(c)` / `assume(c)` bind the hypothesis `c` for everything after them. In an
event handler, effect, timer callback or callback passed to a child, whose
outcome obligations (invariant preservation, robustness, the parent's emit) are
proved outside the body's term, the rest of the body is `if h : c then … else
(no updates, no callback)`: the `else` is unreachable (`c` is proved, or assumed and
reported), and splitting on the `if` hands those obligations `h : c` too. A
timer registered in an effect body is checked under that body's top-level early
returns, asserts and assumes before the registration (§2.6). A
function's `ensures` theorems are proved about its result, outside its body: a
fact inside the body does not reach them (state it as `requires`, or `ensures` of a
helper).

---

## 2. The React model (`lean/VReact/Core.lean`)

### 2.1 State and the update queue

A component's hook state (all `useState`/`useReducer` slots) is a structure
`S`. A setter call does not change the state: React queues an update and
processes the queue after the handler. One setter call is an `Update S := S → S`:

* `setX(v)` ↦ `fun st => {st with x := v}` — `v` was computed from the **render
  snapshot** (the closure's values);
* `setX(f)` ↦ `fun st => {st with x := f st.x}` — functional update;
* `dispatch(a)` ↦ `fun st => {st with r := reducer st.r a}`.

`Outcome.apply` folds the queue over the state — exactly React's batching.
Consequently (proved in `Runtime.lean`): `setN(n+1); setN(n+1)` increments once,
`setN(m => m+1); setN(m => m+1)` increments twice, and a replace-update ignores
earlier queued updates. The regression case `StaleBatch.tsx` is rejected for
this reason; `FunctionalBatch.tsx` is accepted.

### 2.2 Snapshots: discrete events, robust updates, rebasing

React 18 has three event priorities (react-dom 18.3.1 `getEventPriority`).
Only the updates of a *discrete* event (click, input, keydown, submit, …:
the `DiscreteEventPriority` events, a whitelist in `component.ts` and
`Core.discreteEvents`) are flushed synchronously — in a microtask, or at the end of
the event when its ChangeEventPlugin restores a controlled input — so the next
discrete event runs a handler of the latest render, whose snapshot is the current
state. A discrete handler must therefore preserve the invariant **from its
snapshot**. This assumes that React flushes before the next event: true for user
input, which the browser dispatches from native code (a microtask checkpoint after
every listener), and for a script that lets a microtask checkpoint pass between
two calls that dispatch events (`el.click()`, `dispatchEvent`, `el.focus()`), or
wraps each in its own `act` (React Testing Library's `fireEvent`). A script that
makes several such calls in one go — including emulators of browser default
actions, such as user-event's emulation of implicit submission (keydown, then
click and submit) without `act` — is outside the model. What the DOM itself
dispatches *inside* one call — a click's activation behaviour — belongs to that
event; §5 says how VTS keeps it to one handler.

Continuous events (mousemove, scroll, wheel, mouseenter, …), default-priority
events (transitionend, animationend, load, error, media events, …), effects and
asynchronous callbacks (timers) are rendered later and may run with a stale
snapshot, so their outcomes must be **robust**: preserve the invariant from
*every* state that satisfies it; they may not call parent callbacks. This is
what rejects the classic stale-closure bug (`StaleTimer.tsx`) and accepts the
functional-update fix (`RobustTimer.tsx`). Focus and `invalid` events are
discrete in React, but the DOM also dispatches them inside the batch of another
event or of React's commit, before the earlier updates are rendered — `autoFocus`
focuses during the commit (onBlur of the element losing focus, anywhere in the
app, and onFocus of the new one run in one batch, after a trusted click too:
`CxFocusRobust.tsx`), a click on a `<label>` focuses its control, `el.focus()`
fires blur and focus, form validation fires `invalid` at every invalid control —
so `onFocus`, `onBlur`, `onInvalid` (and the composition events, whose fallback
uses `focusout`) are checked robust as well.

**Rebasing.** These *deferred* updates are still pending when a later discrete
event runs. React keeps one update queue per hook; it renders the discrete
update `f` first, skipping a pending deferred `u`, and later re-applies both in
order — `f(u(s₀))`, although `f` was computed from the snapshot `s₀`. So in a
component with deferred sources (an effect or timer that sets state, a
continuous/default-priority handler), its discrete handlers and the callbacks it
implements for children are checked **rebase-safe** (`Core.RebaseSafe`,
obligations `handler-rebased` / `callback-rebased`): from every invariant state
that agrees with the snapshot on the fields no deferred source writes (the
others vary). Components without deferred sources keep the snapshot check
(`RxRebaseTimer.tsx` fails, `RxRebaseTimerOk.tsx` verifies).

Why this is sound. Every VTS update reads and writes a single hook (`setX(v)`,
`setX(p => …)`, `dispatch(a)`), so per-hook queue processing is the in-order
application of whole outcomes. Every state React renders is the initial state
with an in-order subsequence of the queued outcomes applied, in which every
discrete outcome before an included discrete one is included (synchronous
updates are flushed before the next event and never skipped). By induction each
such state satisfies the invariant: a deferred outcome is robust; a discrete
outcome is applied to a state whose non-deferred fields equal its snapshot's
(only discrete outcomes write them, and all earlier ones are applied), which is
what `RebaseSafe` covers. With no deferred fields `RebaseSafe` is the snapshot
check; with all fields deferred it is robustness. `Runtime.rebase_safe` proves
the step for one pending update; `dispatch` itself models the in-order case.

### 2.3 Rendering is proof-carrying

`render : (props) → (state) → pre props → inv props state → VNode …` is a pure
function returning a view tree in which

* every event handler stores the proof that its outcome is safe (§2.2),
* every child element `<C …/>` stores the proof of `C.pre`,
* every keyed list stores the proof that its keys are pairwise distinct
  (React's reconciliation requirement; `int` and `string` keys never mix),
* every expression JavaScript evaluates during render is kept in the term with
  its obligations, including `key={…}` outside lists (`VNode.withKey`; a key
  change remounts, which is covered because both keeping the state and
  re-initialising it are verified) and boolean children (`VNode.ofBool`, rendered
  as nothing),
* every parent callback handed to a child stores the proof that, assuming the
  child's callback contract, the parent's invariant is preserved.

A render function that type-checks in Lean can only ever offer the user
invariant-preserving interactions.

### 2.4 Composition: callbacks as assume/guarantee

A child declares `callbackRequires(props.onPick, (i) => 0 <= i && i < props.n)`.

* **Guarantee (child):** every call `props.onPick(e)` must prove the contract.
* **Assume (parent):** the parent's function passed as `onPick` is verified
  under the contract. In Lean the callback returns an `Emit` — the parent
  outcome packaged with the proof that it preserves the parent's invariant
  against the parent's (current) snapshot.

A handler may invoke at most one parent callback per execution path (two would
compose two parent outcomes that were only checked separately). Several
`callbackRequires` for one callback are conjoined.

### 2.5 Lifecycle obligations

* `init_inv` — mounting (`useState(init)`, `useReducer(r, init)`) establishes the invariant.
* `stable` — when the parent re-renders with new props, React keeps the state:
  `inv props s → pre props' → inv props' s`. An invariant like
  `count <= props.max` is rejected (`PropsStability.tsx`): the parent may lower `max`.

### 2.6 Effects

`useEffect(body, deps)` runs after commit when its dependency values changed.
Its synchronous updates and the timers it registers must be robust and may not
call parent callbacks; `deps` must be exhaustive (otherwise stale closures;
the check sees every reference, including shorthand properties `{ x }`; the same
check applies to `useMemo` / `useCallback`). The model has no cleanup step, so a
returned cleanup is restricted statically: it must be an inline function that
only calls `clearTimeout` / `clearInterval` and makes external writes
(`console.*`, `localStorage.*`, `document.title = …`) with pure arguments,
possibly under `if`/`else` with pure conditions —
no setters, `dispatch`, parent callbacks or local helpers.
Running a robust effect any number of times (StrictMode) is safe.

A timer is registered only by a statement at the top level of the effect body
(`setTimeout(…)` / `const id = setInterval(…)`). Its callback is checked under the
path condition of that registration. That condition is made of the top-level
early returns `if (c) return;` (no `else`) and the `assert(c)` / `assume(c)`
statements before it. The callback captures the same snapshot as the effect: an
effect cannot assign a variable it captures, and a captured `let` is not
reassigned after the effect is created. So the model's task is
`if c then skip else callback` for an early return, and `if c then callback else
skip` for an assert or assume. The `skip` branch stands for a timer the program
never registers, and it does nothing. A condition about the snapshot says nothing
about the state the timer fires against, so `setLeft(l => l - 1)` still needs its
own guard (`CxTimerGuardFail.tsx`). A condition is used only if it translates in
the component's scope without obligations of its own: one that reads a const
local to the effect body is left out, which only weakens the facts.
(`CxTimerGuard.tsx`: the guarded countdown
`if (left <= 0) return; setTimeout(() => setLeft(left - 1), …)`.)

Hooks (`useState`, `useReducer`, `useEffect`, `useMemo`, `useCallback`) are
matched by React by call order, so they must be top-level statements of the
component, before any statement that may return (an `if`, a `switch`, …); a hook
in a branch, loop, handler or closure is rejected.

---

## 3. The runtime and the soundness theorem (`lean/VReact/Runtime.lean`)

The runtime state is a tree of mounted instances (`Inst`): each records the
element that created it (component spec, props, callbacks, render closure), its
state **with the proof of its invariant**, its effect dependencies, its timers,
and its children. A child's callback-result type mentions the parent's current
state, so a child can only hand its parent outcomes proven safe for it.

Transitions:

| transition       | React behaviour modelled |
|------------------|--------------------------|
| `mount`          | initialisers, render, mount children |
| `reconcile`      | match new child elements to old instances by position/key **and component identity**: same component ⇒ keep state (`mount_keeps_state`), otherwise mount fresh (`mount_fresh_state`); removed children unmount |
| `dispatch`       | a discrete event runs one handler of the latest render; its queue is processed; its parent-callback outcome propagates up the instance path; affected instances re-render |
| `flushEffects`   | after commit, effects whose deps changed run (robust), timers are (re)registered |
| `fireTask`       | a timer callback fires against the current state |

**Theorem `run_allInv`.** For every sequence of actions (user events, effect
flushes, timer firings), every mounted instance satisfies its invariant.

The proof is by construction: `dispatch`, `flushEffects`, `fireTask` and
`reconcile` can only be *defined* because each component supplies its
obligations. `vreact verify` instantiates the theorem for every root component
as `App.certificate`; `#print axioms App.certificate` then lists every
assumption the whole application relies on. A fully verified app depends only
on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.

---

## 3½. What the translation looks like

`Stats.tsx` (from the walkthrough):

```tsx
export function Stats(props: StatsProps) {
  requires(props.todo >= 0 && props.doing >= 0 && props.done >= 0);
  const total = props.todo + props.doing + props.done;
  const pct = total === 0 ? 0 : idiv(props.done * 100, total);
  return <div className="stats">…<span>{pct}% done</span>…</div>;
}
```

becomes (abridged) a `VReact.Spec` plus a proof-carrying render:

```lean
def pre (props : Props) : Prop := ((props.todo ≥ 0) ∧ (props.doing ≥ 0)) ∧ (props.done ≥ 0)

def render {E : Type} (props : Props) (κ : Cb props E) (σ : State) (hpre : pre props) (hinv : inv props σ) :
    VReact.VNode State E (inv props) σ :=
  let total := props.todo + props.doing + props.done
  let pct := if h_1 : VReact.JS.eq total 0 = true then 0
             else VReact.JS.floorDiv (props.done * 100) total (by vreact_auto)   -- obligation: total ≠ 0
  VReact.VNode.elem "div" [⟨"className", .str (JS.Str.ofString "stats")⟩] [] (…)
```

The divisor obligation is discharged in a context that contains `h_1 :
¬ total = 0` — the branch condition. Without the guard, the same obligation is
left with `hpre` only, and Lean's goal shows the counterexample
`props.doing + props.done + props.todo = 0`.

---

## 4. What is verified

For every component: initial state satisfies the invariant; the invariant
survives prop changes; every handler (discrete: from the snapshot, or
rebase-safe when the component has deferred updates; continuous,
default-priority, focus/blur/invalid, effects, timers: from any state) preserves it; rendering never
fails (indices, divisions, non-null assertions, preconditions of called
functions — also in keys and boolean children); keys are
distinct; child preconditions hold; callback contracts hold in both directions;
hook rules hold (static checks). For every function: its body is safe and its
`ensures` hold.

## 5. The trusted base — what is *not* verified

* **The translation** from TypeScript to Lean (≈3k lines of TypeScript). It is
  structural and syntax-directed; the regression suite pins its behaviour. Its
  name escaping relies on `src/leanNames.ts` (Lean tokens and root names),
  generated from the Lean environment by `lean/scripts/GenNames.lean`; regenerate
  it when the Lean toolchain or the VReact library changes.
  Each source file is one Lean module `VTS.<path>` (`Defs.lean`: types,
  constants, functions each followed by its `ensures` theorems; `View.lean`:
  components and certificates); files whose module names coincide, also up to
  letter case, are rejected, and so are modules whose generated directories
  differ only in case (`src/lib.ts` and `src/Lib/x.ts`) and modules that would
  generate the same Lean name (`src/a/b.ts` declaring `post` next to a function
  `b` of `src/a.ts` with an `ensures`: both `VTS.a.b.post`; also the names Lean
  derives from a structure or inductive — fields, constructors, `rec`, … —
  and, below another module's function `f`, `f.post`, `f.post2`, …, `f.eq_1`,
  …). Namespaces may otherwise nest (`src/ui/Board.tsx` next to a component
  `Board` of `src/ui.tsx`). User lemmas `proofs/<path>.lean` are imported by
  that module's `View.lean` and by the `Defs.lean` of every module importing it
  (unless that would close an import cycle); `proofs/Base.lean` by every
  `Defs.lean`. When every importing module can import them, the `ensures`
  theorems of the module's functions that no other function or constant of the
  module uses are proved after the lemmas, in `Posts.lean` (imported by the
  module's `View.lean` and the importing modules' `Defs.lean`).
* **The report.** Every obligation runs under `vreact_ob` (`VReact/Budget.lean`),
  with its own heartbeat budget (per obligation also under parallel elaboration:
  Lean's heartbeat counter is per thread, and an obligation runs on one thread; the
  cost of realizing an auxiliary declaration that several obligations share goes to
  the first one that needs it), and reports its result at its marker: the
  information `vreact:ok` when the automation proved it; otherwise a *warning*
  `vreact: …` (failed: the failure text and the goal) or `vreact:blocked …`
  (it depends on `sorry` from a failure elsewhere: its goal contains one, the
  proof found uses one — also through a definition it unfolded, or an
  auxiliary lemma —, it failed on a goal that unfolds to a `hole()`, or Lean
  hid the automation's error because it mentions such a `sorry`), and the goal
  is admitted with `sorry`. A blocked obligation is *not checked*: neither
  proved (a proof through the admitted proof of a false statement proves
  nothing) nor failed. Running out of the budget, goals left over, an error
  the automation logged and a proof that uses a `sorry` the automation made
  are failures, never proofs. (A proof that refers to another declaration whose
  proof was admitted — a callee's failed contract — is a proof modulo that
  contract and counts as proved; the item is `INCOMPLETE` by its axioms.) A failure is not a Lean error, so the module and every module
  importing it are still built and checked; the admitted goal shows as
  `sorryAx` in the axioms of whatever depends on it. `vreact verify` counts an
  obligation as proved only if every copy of its marker has `vreact:ok`, none
  has a failure (a `vreact:` warning or an error), its file was elaborated to
  the end (the `vreact:checked` sentinel), its declaration has no other error,
  and its item's axioms are reported, with any `sorryAx` among them coming from
  a reported failure, hole or error (of the item, an item it uses, or a user
  proof); missing evidence means *not checked*, never proved. Every component,
  certificate, function, contract, constant and fact has a `#print axioms`;
  `sorryAx`, a `declaration uses 'sorry'` warning (other than an admitted
  goal's) or an error in one of its declarations makes it `INCOMPLETE`: an item
  whose own obligations are proved is `INCOMPLETE` when it relies on one that is
  not, and the report names that dependency. `UNCHECKED` (no axiom report) is
  left for items Lean never got to: lake or import errors, an error that stopped
  a file. Lake errors without a position (imports, build cycles) are shown and
  make the result not verified. An axiom report, the sentinel or `vreact:ok`
  counts only when Lean printed it at the
  generator's own `#print axioms X` / sentinel line / `vreact_ob` token, in the
  log lake prints for that generated module's job: lake prints each message as
  text, so a line of another message (a user proof's `#print "…\ninfo: VTS/…"`)
  stays text of that message (and `vreact_ob` drops `vreact:` messages that code
  running inside the obligation logs; several reports for one name are joined).
  A generated declaration
  with an error makes every obligation of its item unproved; when Lean still
  reports clean axioms for its name, something else (e.g. a declaration of a
  user proof) stands in for it, so every item that uses it, directly or not, is
  `INCOMPLETE` as well. An axiom that is neither Lean's standard ones, nor
  `VReact.assumed`, nor emitted for a `@trusted` declaration (e.g. one declared
  in a user proof) makes the items that depend on it `TRUSTED` (the verdict
  says "modulo axioms from outside the translation"), except an axiom of native
  evaluation — `<decl>._native.<tactic>.ax_…` (`native_decide`, `decide +native`,
  `bv_decide`), `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` —
  which trusts Lean's compiler instead of its kernel: the items that depend on it
  are `INCOMPLETE` and the result is NOT VERIFIED (`RlNativeAxiom`).
* **User proofs** (`proofs/**/*.lean`, `proofs/Base.lean`) are imported into
  generated files, so whatever they declare takes effect while the translation is
  checked. Before Lean runs, `vreact` checks every proof file against a whitelist
  (`lean/ProofCheck.lean`, the `vreact-proofcheck` program of the library): it
  parses the file with Lean's own parser, in the environment the file is
  elaborated in (`Init` alone for a file without imports, otherwise `VReact`;
  `open`/`namespace`/`section`/`end`/`set_option` are elaborated, so scoped syntax
  and options are what Lean will see), rejects a file that does not parse
  completely, and accepts only: plain `import`s of `VTS.…`, `Proofs.…`, `VReact`
  and `Init` modules; `theorem`, `def`, `abbrev`, `example` (modifiers: doc
  comment, the attributes below, `private`, `protected`, `noncomputable`,
  `nonrec`) declared outside the namespaces `VTS` and `VReact` and not named like a
  `VReact.` name; `open`, `namespace`/`section`/`end` (not under `VTS` or
  `VReact`), `variable`, `universe`, `include`, `omit`, module docs, `#check`,
  `#print`; the attributes `simp`, `vreact_simp`, `grind …` (also `local`, and
  erased with `attribute [-…]`) and `grind_pattern`; `set_option` of
  `maxHeartbeats`, `maxRecDepth`, `synthInstance.maxHeartbeats`/`maxSize`,
  `autoImplicit`, `relaxedAutoImplicit`, `diagnostics`, the registered `linter.*`
  and `pp.*` options with a Bool or Nat value, and `trace.C` for a registered
  trace class `C` (not `trace.profiler` and its options: `trace.profiler.output`
  writes a file, `trace.profiler.serve` starts a web server and the browser and
  blocks the build) — as a command, with `in`, and inside terms and tactics; and
  in terms and tactics anything but `run_tac`, `by_elab`, `unsafe`, `include_str`,
  `native_decide`, `+native`, a `decide (config := …)` value (`⟨false, true, true,
  false⟩` is `+native`; write `+kernel`, `+revert`, …), the `bv_decide` tactics
  (also in `grind =>`/`sym =>`; they run an external SAT solver), `idbg`, the
  library's test tactics and the `Lean.ofReduceBool` family. String, character
  and name literals and names may not contain line breaks or other control
  characters (also as escapes): Lean prints them in its messages, where such a
  line could read like a message about a generated file. Everything else — `axiom`, `instance`
  (also `deriving`, `@[instance]`), `opaque`, `structure`/`inductive`, `macro`,
  `macro_rules`, `syntax`, `notation`, `elab`, simprocs, `#eval`, `run_cmd`,
  `initialize`, `export`, `mutual`, `partial`, any other attribute
  (`implemented_by`, `extern`, `reducible`, …) or option (`debug.skipKernelTC`, …)
  — is rejected with its file:line and text. What remains can only state and prove
  propositions and tag them for the automation: their proofs are kernel-checked,
  and what they rely on (`sorryAx`, an axiom of a dependency) shows in the axiom
  report of every item that uses them. The trusted parts are Lean's parser and
  this whitelist. (For an independent replay of every generated and proof
  declaration through the kernel, run `lake env leanchecker VTS Proofs` in
  `.vreact/`.)
* **The JS runtime model** (`JS.lean`): e.g. that `Array.prototype.slice` behaves
  like `JS.slice`. Definitions follow ECMA-262 directly; where ECMA-262 leaves a
  result implementation-defined (`toSorted` with an inconsistent comparator) the
  model fixes only what every engine guarantees (a permutation).
* **The React model**: that React 18 behaves as described in §2–3 (discrete-event
  flushing, per-hook update queues and rebasing, reconciliation by
  position/key/type), and the event table of `component.ts` (React handler prop
  → native events → priority), which mirrors react-dom 18.3.1's event plugins
  and `getEventPriority`. Rebasing is covered by the argument of §2.2 (with
  `Runtime.rebase_safe`), not by `dispatch`.
* **Abstractions:** integers are unbounded, and an `int` is a mathematical
  integer; values are JS values up to the sign of zero, which no accepted
  operation observes (a division needs a divisor that is not zero, §1.2);
  numbers are opaque to proofs (above); Unicode
  case mapping is opaque; `localStorage`, `console`, `document.title` writes are
  external effects with no state change; reading external data is not modelled.
* **Outside the subset:** the entry point (`main.tsx`), React itself, the DOM,
  CSS.
* **Event bubbling, multi-handler events and activation behaviour** are handled
  by a static restriction rather than modelled: the runtime runs one handler per
  event, and VTS rejects every layout in which one event — one native dispatch
  together with what the DOM dispatches synchronously inside it (§2.2) — could run
  two discrete handlers, or one twice, before React renders:
  - two props of one element dispatched by the same native event (a checkbox's
    `onClick` and `onChange` both run on `click`; `onInput` and a text input's
    `onChange` both run on `input`: react-dom's ChangeEventPlugin);
  - an element with handlers containing a descendant handler that shares a
    native event (e.g. `<li onClick>` around a checkbox's `onChange`) or a user
    component;
  - a click's activation behaviour, which runs before React renders when a
    script dispatched the click (`el.click()`, `dispatchEvent`, testing libraries,
    jsdom): a submit button (`<button>` other than `type="button"`/`"reset"`,
    `<input type="submit">`/`"image"`, or a dynamic `type`) fires `submit` at its
    form, a reset button `reset`. Which button a click inside a button activates
    is browser-specific. The DOM specification (and jsdom) activates the
    innermost element with an activation behaviour. Chromium dispatches
    `DOMActivate` at the click's target as its default action. That event
    bubbles to the enclosing `<button>`, which submits, resets or invokes,
    unless the target handled the click itself. Only a checkbox, a radio
    button and a link (`<a href>`) do that, and each only for a click on
    itself. A click on a nested `<button>`, on an `<input>` of another type,
    on a `<select>`, `<textarea>`, `<summary>`, `<details>` or `<img>`, or on
    the content of a link inside the button activates the button (Chromium 152,
    react-dom 18.3.1). VTS covers both behaviours.
    Rejected: `onClick` on such a button, on an element around it, or on an
    element inside it, except a checkbox, radio button or `<a href>` with a
    static `type`/`href`. This applies when the button's form submit/reset
    reaches `onSubmit`/`onReset` (on its form or above), or when the button
    names its form with `form=…` (which may be anywhere). Also rejected: a
    `<label>` inside such a button, with or without handlers (one click on the
    label activates the button twice, once for the label's click and once for
    the click it dispatches to its control), another such button inside it,
    and a user component inside it. The same for an invoker button
    (`commandfor`/`command`): its command runs on an element anywhere, and
    `request-close` fires `cancel` at a dialog synchronously (`onCancel`).
  - A `<label>` dispatches a click on it (or on non-interactive content inside
    it) again to its control — the element `htmlFor` names, or its first form
    control — after focusing it; when the control is inside, that click passes
    the label and its ancestors again. Interactive content stops this, for
    itself and everything inside it: `<button>`, `<label>`, `<select>`,
    `<textarea>`, `<details>`, `<input>` other than `type="hidden"`, and
    `<a href>`. A `<summary>` is not interactive content. Chromium treats a
    `<summary>` outside a `<details>` as plain content, and a details' own
    summary is inside the `<details>`, which stops the label. Rejected:
    `onClick` on a label, on an element around a label, or on an element inside
    a label that is not interactive content and not inside any; a user
    component inside a label.

  Checked safe, so accepted (with react-dom 18.3.1 under jsdom 25 and in
  Chromium): a checkbox's or radio's `click` is followed by
  `input`/`change` only after React has rendered (its ChangeEventPlugin flushes
  to restore the controlled input), so `onInput` there sees the new state;
  `<details>` fires `toggle` in a later task (and `onToggle` is robust); links
  navigate later; a `popovertarget` button fires `beforetoggle` (no React 18
  prop) and a later `toggle`, and a dialog's `close` event is a later task too;
  implicit submission by Enter and the keyboard activation of a
  button follow trusted key events only (a scripted `keydown` has no default
  action), which the browser dispatches from native code with microtask
  checkpoints in between. Focus and `invalid` events, which the DOM also fires
  inside other batches (label activation focuses the control; `autoFocus`
  focuses during React's commit; validation on submit), have robust handlers
  (§2.2), and robust handlers cannot call parents, so several of them in one
  batch compose with each other and with the one discrete handler. `onSelect`
  and capture-phase handlers are rejected; unknown handler names are rejected,
  never discrete.

Lean's kernel checks every proof; `sorry`, `@trusted` and `assume(…)`
(`VReact.assumed`, reported `ASSUMES`) show up in the axiom report, so nothing
unverified can be mistaken for verified.

`vreact synth` is not part of the trusted base: its random tests only prune
candidates. It reports "proved by Lean" (and `--write` writes a fill) only when
Lean elaborated the function and all its postcondition theorems, none of the
function's obligations failed, and their axioms contain no `sorryAx` — so a
function with several holes is proved once all are filled, a `@trusted`
function is refused, and a failure elsewhere that keeps the function from being
checked is reported as "not proved". The written text is the text Lean checked.
A proof whose axioms include @trusted declarations or `assume(…)` facts is
reported relative to them (`--json`: `"status": "proved-relative"` and
`relative_to`). Synth types candidates with the narrowing the translator has at
the hole (with the variants left after exclusions, which the translator splits
on when a fill needs them), and searches a hole once per fill of the earlier holes a call can
also evaluate (holes in different cases or branches are searched once); both
only steer the search — Lean still checks every fill of a function together.
