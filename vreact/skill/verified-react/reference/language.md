# VTS language reference

VTS is TypeScript + TSX with contracts from `vreact/spec`. Code outside the
subset is rejected with a message saying why and what to use instead.

## Modules

A verified module may contain: `import`s (from `react`, `vreact/spec`, and other
verified modules — no cycles), `type`/`interface` declarations, `const`s,
functions, and components (capitalised functions returning JSX). Nothing else
at top level.

Each file becomes the Lean module `VTS.<path>`: its path under `src` without
`.ts`/`.tsx`, characters other than letters, digits and `_` replaced by `_`.
Two files that map to the same module, or to names differing only in letter
case, are rejected (`module name clash`): e.g. `limits.ts` + `limits.tsx`,
`my-x.ts` + `my_x.ts`, `todo.ts` + `Todo.tsx`. Rename one of them.

The tsconfig needs `"strict": true` (with `strictNullChecks` and `noImplicitAny`) and `"lib": ["ES2023", "DOM"]` (for
`toSorted`/`toReversed`/`with`); without a tsconfig, vreact uses these defaults.

## Types

| write                                   | notes |
|-----------------------------------------|-------|
| `boolean`, `string`, `int`              | `int` = integers (`import { type int } from "vreact/spec"`) |
| `number`                                | IEEE float: allowed, but proofs cannot reason about values |
| `"a" \| "b" \| "c"`                     | string-literal enums (`switch` on them is exhaustive) |
| `{ readonly f: T; g?: U }`              | records (optional field = `U \| undefined`) |
| `{ kind: "x"; … } \| { kind: "y"; … }`  | discriminated unions — any common string-literal field works |
| `readonly T[]`, `T \| null`, `[A, B]`   | lists, options (not both null and undefined), tuples |
| `(a: A) => void`                        | only as callback **props** |

Not supported: `any`, generic types (generic type aliases and interfaces; generic
*functions* are, see Generics), classes, `Map/Set/Record`, recursive types,
non-discriminated unions (`string | number`), `ReactNode`/`children` props.

## Expressions

* Arithmetic `+ - *` on `int` (also where `int | null` is expected: computed at
  `int`, then wrapped); `/` produces `number`; use `idiv(a, b)` or
  `Math.floor(a / b)` for integer division (obligation: `b !== 0`); `%` (obligation).
  Unary `+` only on numbers (`+s` on a string is rejected: ToNumber is not modelled).
* Comparisons `< <= > >= === !==`. `===` on objects/arrays (also `T | null` of
  them) is rejected (identity); compare keys/fields. `===` on `number` is IEEE
  (`NaN !== NaN`), in code and contracts. `== null` / `!= null` allowed.
* `null` vs `undefined`: `x === null` / `x === undefined` must name the nullish
  value `x`'s type actually has — optional fields `f?: T`, `find()`, `at()` and
  `?.` give `undefined`; `T | null` gives `null`. A strict test that is always
  false (`t.due === null` on `due?: int`), or on a value that may be either, is
  rejected: use `== null`. Two optional values compared with `===` must use the
  same nullish value.
* Annotations of function parameters must be exactly the type of the value
  received (or be left out): `ensures((r: T) => …)` with `T` the declared return
  type, a `callbackRequires`/handler parameter the callback's parameter type, a
  functional update's the state type, an array callback's the element type (`int`
  for an index; `number` also works for an int). TypeScript does not check these
  (`(v: unknown) => …`, `(r: int | null) => …` for an `int | undefined` value pass
  it), so others are rejected; so are default values, `?` and rest parameters there.
* An unannotated `ensures((r) => …)` parameter is `any` to TypeScript: passing `r`
  (or `r.f`, `r[i]`) where the type tells null from undefined (`isNull(r)` with
  `isNull(x: int | null)`, `xs.includes(r)`, `{ f: r }`) is rejected unless its
  nullish value, from the return type, is that one. Annotate `r` with the return
  type to have TypeScript check it.
* `+` with a string operand concatenates; `int`, `boolean` and enum operands are
  converted as in template literals (`x + "px"`); a `number` or nullable operand is
  rejected (use an int, or `${n}`). Bitwise operators (`~ & | ^ << >> >>>`) and
  compound assignments other than `+=`/`-=` are rejected.
* Widening as in TypeScript: an `int[]` where `(int | null)[]` is expected
  (elementwise, also in a spread), an enum member where a `string` is expected
  (`return k;`, `k === s`). The same inline object type or string-literal union
  in one module is one type (e.g. `hole<{ readonly v: int }>()` returned from a
  function declared to return `{ readonly v: int }`).
* `&& || ! ?: ?? ?.` (also `a ?? b ?? 0`) and template literals.
* `xs[i]` (obligation: `0 <= i < xs.length`), `t[0]` on tuples, `x!` (obligation).
* Arrays: `length map filter some every find findIndex includes indexOf slice
  concat join reduce(f, init) toSorted(cmp) toReversed with at flatMap`, spread.
  Lambdas inline: `xs.filter((x) => x.id !== id)` (they may ignore parameters:
  `xs.map(() => "")`). Exact arities: optional arguments that are not modelled
  are rejected (`thisArg`; `includes(v, fromIndex)` → `xs.slice(k).includes(v)`;
  `indexOf(v, fromIndex)`). `includes`, `indexOf` and `distinct(xs)` without a
  key need primitive elements (`boolean`, `int`, `string`, enums, options of
  them): on records/arrays/tuples JS compares identity (use `some`/a key), on
  `number` SameValueZero. `find`/`at` on arrays of optional values are rejected
  (a found `null` and "not found" would be conflated).
  `toSorted`: proofs know the result is a permutation (length, membership,
  `distinct` keys); the *order* is known only for a consistent comparator
  (ECMA-262: `cmp(a, a) = 0`, symmetric ties, transitive — e.g. `(a, b) => a.k - b.k`;
  `(a, b) => a.k < b.k ? -1 : 1` is not consistent: JS engines order its ties
  differently; Lean lemmas `JS.consistent_sub`, `JS.pairwise_toSorted`,
  `JS.pair_sublist_toSorted` state the order for `proofs/`). Rejected on arrays that
  may contain `undefined`.
* Strings: `length trim includes startsWith endsWith slice repeat toLowerCase
  toUpperCase` — exact UTF-16 semantics (case mapping is opaque to proofs),
  including literals with lone surrogates (`"\uD800"`). No position arguments:
  `s.includes(t, p)` / `s.startsWith(t, p)` → `s.slice(p).includes(t)` (`p >= 0`),
  `s.endsWith(t, e)` → `s.slice(0, e).endsWith(t)`.
* `Math.max/min/abs/sign/floor/trunc/round/ceil`, `String(x)`.
* Names: any identifier works. Ones that are Lean keywords or root names
  (`matches`, `rec`, `show`, `max`, `List`, …) get a `'` in Lean (`VTS.m.max'`),
  also components (`function Type()` → `VTS.m.Type'`); names shaped like Lean's
  derived instances (`instReprP`: `inst` + capital) get `''`, and a *type* of that
  name is rejected (rename it). Enum members may be any
  strings (escaped into distinct constructors). File/directory names that
  are such names get a `_` (`src/end/Sort.tsx` → `VTS.end_.Sort_`, lemmas in
  `proofs/end_/Sort_.lean`).
* Calls to verified top-level functions (their `requires` become obligations)
  and to local helper arrows (inlined).
* Narrowing: `x !== null`, `x.kind === "add"`, `switch (x.kind)`, early returns —
  fields of the narrowed variant become available, also inside handlers created there.
  The complement narrows too when one variant is left (`if (s.kind === "a") return …;
  return s.onlyInB;`, `else`, `s.kind === "a" || s.b > 0`, `c ? … : s.b`), also after
  several exclusions; with several variants left, the fields they share are available.
  A `T | null` value tested non-null and then to be a variant is that (present) variant.
  Assigning a present value to a `let x: T | null` (`x = 0`, `let x: int | null = 3`)
  narrows it too; assigning again (or in a loop) forgets it.

## Statements

`const`, `let` + reassignment (locals only), `if/else`, `return`, `switch`
(cases end with `return`/`break`, also `case "x": { …; break; }`; no fall-through;
`default` anywhere, also grouped `case "a": default:`; on an int/string/boolean/number:
literal, negated-literal or constant labels compared with `===`, a non-integer label
on an int is rejected; on an enum or `x.kind`: string literals), `for (const x of xs)` (may
assign outer `let`s; no `return`/`continue` inside, `break` only to end a `switch`
case), `throw` (must be provably
unreachable), `assert(c)`, `assume(c)`. No `while`, `try`, `var`, recursion.

Closures and `let`: JS closures read a variable when they run. So a function
that runs later (helper arrow, handler, callback prop, `setX(prev => …)`, effect,
timer, cleanup, `useCallback`) may not read a `let` that is reassigned after the
function is created — copy it first: `const capNow = cap;`. No function or
callback (array callbacks included) may assign a `let` declared outside it —
use `for…of` or `reduce`. Array callbacks may read outer `let`s.

## Contracts

```ts
export function f(x: int, xs: readonly int[]): int {
  requires(0 <= x && x < xs.length);          // first statements
  ensures((r: int) => r >= 0);                // r: exactly the return type (or no annotation)
  …
}
/** @opaque */  …   // callers see only requires/ensures
/** @trusted */ …   // body not verified, contract assumed (reported)
```

Several `requires` form one precondition, in order: a later one may rely on an
earlier one (`requires(xs.length > 0); requires(xs[0] >= 0)`); the same holds for
a component's `requires` and `invariant`s. Inside contracts,
guards are in scope as JS evaluates them: the right side of `&&` / `||`, the
branches of `?:`, the consequent of `implies(a, b)`, and quantifier bodies
(`forall(0, xs.length, (i) => xs[i] >= 0)`, `xs.every((r) => r[0] > 0)`) may index
under their guard.

Constants: small ones are unfolded wherever used. For large data use

```ts
/** @opaque */
export const SEATS: readonly Seat[] = [ /* … */ ];
assert(distinct(SEATS, (s) => s.id));            // module-level fact, proved once
assert(SEATS.every((s) => 0 <= s.row && s.row < 3));
```

Module-level `assert`s must mention an `@opaque` constant declared above them.

Spec helpers (usable in code and contracts): `forall(lo, hi, i => …)`,
`exists(lo, hi, i => …)`, `distinct(xs, x => key)`, `implies(a, b)`,
`idiv(a, b)`, `range(n)`. `hole<T>()` is a synthesis placeholder.

## Generics

```ts
export function firstOr<T>(xs: readonly T[], d: T): T { … }                        // no constraint
export function countKey<K extends int | string>(xs: readonly K[], k: K): int { … } // equality
export function byId<T extends { readonly id: int }>(xs: readonly T[], id: int): T | undefined { … } // fields
```

Top-level functions may have type parameters (exported or not, also `@opaque`
and `@trusted`). A type parameter may appear in parameter and return types,
local annotations (also of helper arrows and callback parameters), `hole<T>()`,
arrays, `T | null` and tuples — not inside object types (`{ readonly v: T }`:
pass the value as its own parameter). At most one constraint per parameter:

* **none** — values of `T` are abstract: they can be passed, stored (arrays,
  `T | null`, tuples), returned, given to other generic functions, and used with
  the array methods that do not compare elements (`map filter some every find
  findIndex slice concat toReversed toSorted(cmp) with at reduce flatMap`,
  `length`, spread, indexing).
* **equality** — `K extends int | string | boolean | "a" | Color` (unions of
  these; `Color` a string-literal enum type): also `===`/`!==` on `K`,
  `includes`, `indexOf`, `distinct(xs)` and `distinct(xs, x => k)` with a `K` key.
  `K extends number` is rejected (`NaN !== NaN`; use `int`).
* **fields** — `T extends { readonly id: int; readonly note?: string }` (or the
  name of a record type): `x.id` on `x: T` (an optional field is `U | undefined`).
  Field types may not mention type parameters. Equality and fields cannot be
  combined (no intersections).

Even under `T extends int` or `T extends string` the values of `T` are abstract:
no arithmetic, ordering, string conversion (`${x}`, `+`), string properties or
methods, comparison with a value of another type, and no object literal of type
`T` (the body is checked once, for every type `T` may be). Null tests on `T | null`
work (a type parameter is never instantiated with a nullable type).

Calls infer the type arguments from the VTS types of the arguments (where
TypeScript cannot tell `int` from `number`: `count(xs, 1.5)` instantiates
`number`), then from the type the result must have (`const xs: readonly int[] =
emptyOf()`), then for `[]`, `null` and literals; two arguments of `int` and
`number` give `number`, an enum and a `string` give `string`. Otherwise write the
type arguments (`emptyOf<int>()`; "cannot infer T"). Each call is checked: an
instantiation is never nullable (`firstOr(xs, null)` with `xs: (int | null)[]` is
rejected — give the function a `T | null` parameter instead), never `number` for
an equality constraint, and for a field constraint is a record (or a union, in
every variant, or another type parameter with that field) whose field has exactly
the constraint's type and the same `null`/`undefined`. An argument for a parameter
`T | null` must be `null` (not `undefined`) when absent, as the declared type says
(TypeScript would absorb `undefined` into `T`); likewise for `T | undefined`.

A generic function is proved once for every instantiation, and its `ensures`
hold for every type: a contract that is true only at the module's own calls is
not proved. Callers of an `@opaque` generic function reason with these contracts
at whatever type they call it (also at their own type parameters).

Rejected: generic type aliases and interfaces, generic components, generic
reducers (`useReducer`), generic arrow functions, function expressions and
function types, default type arguments (`<T = int>`), `const` type parameters,
other constraints (`unknown`, `any`, `object`, `keyof`, unions of object types,
intersections, constraints mentioning a type parameter), recursion.

## Components

Order inside the body:

1. `requires(…)` — props precondition (what every parent must establish);
2. `callbackRequires(props.cb, (args) => …)` — what this component guarantees
   about the arguments it passes to callback props (the parent may rely on it;
   several for one callback are conjoined);
3. hooks: `const [x, setX] = useState<T>(init)`, `const [s, dispatch] =
   useReducer(reducer, init)`, `useEffect(() => {…}, [deps])`,
   `useMemo(() => v, [deps])`, `useCallback(fn, [deps])` — top level,
   unconditional, before any `if`/`switch`/early return (never in branches,
   loops, handlers or closures); deps exhaustive (`{ x }` reads `x`);
4. `invariant(…)` — over props and state;
5. render-local `const`s, helper arrows, handlers;
6. `return <JSX/>` (early returns allowed).

Props: a single parameter `props: P` (or destructured `{ a, b }: P`) where `P`
is a record whose function-typed fields are callbacks (`=> void`, required).

Handlers (`onClick`, `onChange`, `onSubmit`, `onKeyDown`, …): arrow functions or
local closures; the event parameter supports `e.target.value`,
`e.target.checked`, `e.key`, `e.preventDefault()`. Setters, `dispatch`, at most
one parent callback per path. Only React's discrete events (`onClick`,
`onChange`, `onInput`, `onKeyDown`, `onSubmit`, …) are
checked from the render snapshot; continuous (`onMouseMove`, `onScroll`,
`onMouseEnter`, …) and default-priority events (`onTransitionEnd`,
`onAnimationEnd`, `onLoad`, `onError`, media events, …) must be robust and may
not call parent callbacks — and so must `onFocus`, `onBlur` and `onInvalid`: the
DOM also fires them inside another event's batch (`autoFocus`, a label click
focusing its control, form validation). In a component with such handlers or with effects /
timers that set state, discrete handlers and callbacks passed to children must
also be safe when React rebases them onto those pending updates (guard inside the
functional update: `setR(p => p.lo < p.hi ? … : p)`). Rejected: unknown handler
names, `onSelect`, capture-phase handlers (`onClickCapture`).

Effects: setters and timers (`setTimeout`/`setInterval` callbacks become tasks;
register them at the top level of the effect body; a timer's callback may use the
early returns `if (c) return;` and the `assert`/`assume` before it, as in
`if (left <= 0) return; setTimeout(() => setLeft(left - 1), 1000)`),
external writes (`localStorage.setItem`, `document.title = …`, `console.*`) are
allowed and have no modelled effect; no async. A cleanup is an inline
`() => { … }` that only calls `clearTimeout`/`clearInterval` and makes those
external writes, possibly under `if`/`else` (`if (id !== null) clearInterval(id)`;
no setters, `dispatch`, parent callbacks or local helpers: it runs later with a
stale render's values and is not verified).

JSX: intrinsic elements with string/int/bool/enum attributes (`className`,
`value`, `checked`, `disabled`, `placeholder`, `type`, …; no `style`, `ref`,
spread), child components with all their props, `{cond && <X/>}`, ternaries,
`xs.map(x => <El key={…}/>)` (keys `int` or `string`, distinct), text from
strings/ints/enums (booleans render nothing, but are checked). `key={…}` outside
lists is checked too (JS evaluates it). A JSX const (`const row = <p>{e}</p>;`)
is checked where it is declared, even if it is rendered only under a condition or
not at all (JS evaluates it there); JSX only appears in a component's render.
`children` props are not supported yet.
One native event may reach at most one discrete handler: an element may not
combine handlers fired by the same native event (a checkbox's `onClick` +
`onChange` both run on click; `onInput` + a text input's `onChange` both run on
input), and an element with a handler may not contain a handler fired by the
same native event (`<li onClick>` around `<input type="checkbox" onChange>`)
or a user component. A click also runs what it activates: a submit (reset) button
submits (resets) its form, and a `<label>` clicks its control again. So no `onClick`
on, around or inside a submit/reset button whose form has `onSubmit`/`onReset`
(or that has `form=…`), or an invoker button (`commandfor`): use `type="button"` or
put the logic in `onSubmit`. Inside such a button only a checkbox, a radio button
or an `<a href>` may have `onClick`. In Chromium a click on anything else inside
it, including a nested button or a text field, also activates the button. No
`<label>` or second such button may go inside it either. No `onClick` on, around
or inside a `<label>`, except on interactive content in it (a control, a button,
a link, a `<select>`, a `<details>`) and on elements inside that content. A
`<summary>` alone does not count. No user component may go inside such a button
or a label (use `htmlFor`).

## Not yet supported (workarounds)

| feature | workaround |
|---------|-----------|
| `useRef`, `useContext`, custom hooks | lift state up / pass props; inline hook calls |
| `children` / `ReactNode` props | compose in the parent |
| recursion, `while` | `for…of`, array methods |
| generic type aliases, interfaces, components, reducers and arrows | concrete types; generic top-level functions (see Generics) |
| `async`, fetch | keep I/O in an unverified module that calls verified reducers |
| guarded updates in `vreact synth` | write the guard by hand with a hole per branch; synth fills straight-line code (all holes of a function are proved together; a hole per `case`/branch is searched once) |
| `vreact synth` on a function whose contract's Lean statement mentions a function that still has a hole (called in the contract, or in the body or `requires` of a function it calls; not in a `@trusted` body or a callee's `ensures`) | not searched ("the contract depends on unfinished function f"): fill or write `f` first |
| `vreact synth` on a `/** @trusted */` function or a component | refused (Lean checks nothing in a trusted body): remove `@trusted` / move the expression into a model function |
| a reducer over a discriminated union calling `@opaque` model functions | supported (contracts are instantiated inside the `switch` arms) |
| invariants about sums (`reduce`) under filter/map | provable, but needs a Lean lemma in `proofs/` (automation handles append, filter, map, `slice`, `toSorted`, `toReversed`, `with` (also swaps `xs.with(i, xs[j]).with(j, xs[i])`), `indexOf`/`findIndex` ranges, `range`, membership, `distinct`, concatenation of string literals, and counts `xs.filter(p).length` under append, delete-by-id, map-updates and mark-all) |
