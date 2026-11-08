# VTS language reference

VTS is TypeScript + TSX with contracts from `vreact/spec`. Code outside the
subset is rejected with a message saying why and what to use instead.

## Modules

A verified module may contain: `import`s (from `react`, `vreact/spec`, and other
verified modules — no cycles), `type`/`interface` declarations, `const`s,
functions, and components (capitalised functions returning JSX). Nothing else
at top level.

* Imports name the file that runs, by themselves: TypeScript-only resolution
  settings (tsconfig `paths`, `baseUrl`, `rootDirs`, `moduleSuffixes`) do not
  change what the bundler loads. So a verified module is imported by its path
  relative to the importing file — `"./model"`, `"../model.ts"`, `"./lib"` (its
  `index.ts`), `"./model.js"` (for `model.ts`) — and that path must lead a
  bundler to the same file (`"./b"` next to both `b.js` and `b.ts` is `b.js` for
  Vite: rejected); `react` and `vreact/spec` (also the `react/jsx-runtime` that
  JSX imports) must resolve to the installed packages, with or without `paths`.
  Bare specifiers that reach a project file (`"@/model"` through `paths`,
  `"model"` through `baseUrl`) are rejected.
* Exports: `export` on declarations, `export { a, b as c }`, `export default f`
  / `export default x` (a name; `export default <expression>` is rejected —
  declare a `const` and export that), re-exports `export … from "./m"` (they load
  `./m` like an import: same rules, cycles included). The bundler compiles each
  file on its own, so VTS type-checks with `"isolatedModules"` (whatever the
  tsconfig says): a type imported from another module is re-exported with
  `export type { Item }` / `export { type Item } from "./types"`, never
  `export { Item }` or `export default Item` (the bundler would keep the export of
  a name the other module does not export: the module would not load).
* A module's top-level code runs in source order when it loads, and reading a
  `const` before its declaration has run throws. TypeScript only flags direct
  reads; VTS also rejects a constant initialiser, `export default x` or
  module-level `assert(…)` that reaches a constant declared below it through
  the functions it calls (`function g() { return B; } const A = g(); const B = 2;`),
  also through a shorthand property (`return { B };` reads `B`).
  Declare constants before the code that uses them (a function may be declared
  anywhere; the lambda of `ensures` may mention a later constant).
* Every source file must be a module (have an import or export). Rejected:
  `declare …` (ambient declarations), `declare global`, `declare module`,
  namespaces, interface merging (an interface declared twice), function
  overloads, and project `.d.ts` files in the program (`/// <reference path>`,
  tsconfig `typeRoots`/`types`/`paths`): they change the types of library or
  React declarations unchecked. Installed packages (`node_modules`) are trusted
  like the TypeScript libraries.
* Library names are recognised by what they resolve to, not by their spelling:
  `undefined`, `Math`, `String`, `console`, `localStorage`, `document`, timers,
  React's hooks (also `React.useState`, `import { useState as useS }`), the
  `vreact/spec` functions and `int` (also `import { type int as I }`), and the
  types `ReadonlyArray`/`Array`, `ReactNode`/`JSX.Element`. A local, parameter,
  import or project declaration spelled like one is that binding (a local
  `const undefined = 3` is 3; `import * as Math from "./m"` is rejected where
  `Math` is used: rename it). React's hooks must come from an import of `react`
  (`import { useState }` or `import * as React`): React's types also declare a
  global `React`, which a module bundle does not define, so tsconfig
  `"allowUmdGlobalAccess"` is rejected.
* TypeScript's checks are part of VTS: `// @ts-ignore`, `@ts-expect-error` and
  `// @ts-nocheck` are rejected anywhere in a verified file, in any letter case
  and with any suffix (`@ts-ignored`, `@ts-ignore-next-line`, `@TS-NOCHECK`: all
  silence TypeScript), also inside a string or another comment.
* Comments that change what the bundler does are rejected anywhere in a file
  (also in a string), in any letter case: JSX pragmas (`@jsx`, `@jsxRuntime`,
  `@jsxImportSource`, `@jsxFrag`: esbuild and Babel read them in any comment, not
  only at the top) and bundler annotations (`/* @__PURE__ */`, `#__PURE__`,
  `@__NO_SIDE_EFFECTS__`, …: a production build deletes an annotated call whose
  result is unused, state updates included).

Each file becomes the Lean module `VTS.<path>`: its path under `src` without
`.ts`/`.tsx`, characters other than letters, digits and `_` replaced by `_`.
Two files that map to the same module, or to names differing only in letter
case, are rejected (`module name clash`): e.g. `limits.ts` + `limits.tsx`,
`my-x.ts` + `my_x.ts`, `todo.ts` + `Todo.tsx`. Rename one of them. Within a
module, types and values share Lean's one namespace: a function or constant
named like a type of its module (`type Limits = …; const Limits: Limits = …`)
is rejected.

The tsconfig needs `"strict": true` (with every check of the strict family:
`strictNullChecks`, `noImplicitAny`, `strictFunctionTypes`, … none set to false)
and `"lib": ["ES2023", "DOM"]` (for `toSorted`/`toReversed`/`with`); without a
tsconfig, vreact uses these defaults. JSX must be React's automatic runtime:
`"jsx": "react-jsx"` (no other `jsxImportSource`, no `@jsx…` comment pragmas).
Compiler options are a whitelist: the usual language, module, strictness, emit
and output options are accepted; options that switch checks off (`"noCheck"`,
`"noLib"`, `"noResolve"`, the removed `suppress…` options, `"resolvePackageJson…":
false`) and any option vreact does not know (`"jsxFactory"`, newer ones) are
rejected with the option's name. The tsconfig.json read is the one in the project
root; a `tsconfig.json` inside the source directories is rejected (the bundler
compiles a file with the nearest one's settings, e.g. its `jsxImportSource`).

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

Not supported: `any`, generics, classes, `Map/Set/Record`, recursive types,
non-discriminated unions (`string | number`), `ReactNode`/`children` props,
library types (`Date`, `HTMLElement`, …). Function types and React nodes are not
data: a parameter, result, constant, state, local, data prop, callback parameter,
local helper parameter or result, or `hole<T>()` whose type contains one (also in
an array, option, tuple or record) is rejected; only a direct field of a
component's props may be a function.

Field names (records, union variants, props): `__proto__` is rejected (in an
object literal `{ __proto__: v }` sets the prototype and creates no field), and so
is an *optional* field named like a member of `Object.prototype` (`toString?`,
`constructor?`, `__lookupGetter__?`, …): when it is absent, reading it gives the
inherited member, not `undefined`. Such names are fine for required fields.

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
  and to local helper arrows (inlined). A helper's parameters need annotations;
  default values, rest (`...xs`), optional (`x?`) and `this` parameters are
  rejected (each gives the parameter another value than the argument: declare
  `x: T | undefined` and pass it, take an array). The arguments and the result
  of an inlined helper are data: a parameter or result annotation with a
  function type or a React node is rejected (a helper that returns JSX is not
  supported); a helper used as an event handler takes the event.
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
a component's `requires` and `invariant`s. A reducer's `requires` may mention
only the action (React may apply a queued action to any state): it becomes a
`precondition` obligation at every `dispatch(…)`. Inside contracts,
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

Module-level `assert`s must mention an `@opaque` constant declared above them in
the same module (a fact about an imported constant is stated in its module).
They may call functions declared anywhere in the module (function declarations
are hoisted) and mention other constants declared above them; the fact is proved
once everything it mentions is defined, and declarations after that point can use
it.

Spec helpers (usable in code and contracts): `forall(lo, hi, i => …)`,
`exists(lo, hi, i => …)`, `distinct(xs, x => key)`, `implies(a, b)`,
`idiv(a, b)`, `range(n)`. `hole<T>()` is a synthesis placeholder.

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
| generics | monomorphic helpers |
| `async`, fetch | keep I/O in an unverified module that calls verified reducers |
| guarded updates in `vreact synth` | write the guard by hand with a hole per branch; synth fills straight-line code (all holes of a function are proved together; a hole per `case`/branch is searched once) |
| `vreact synth` on a function whose contract's Lean statement mentions a function that still has a hole (called in the contract, or in the body or `requires` of a function it calls; not in a `@trusted` body or a callee's `ensures`) | not searched ("the contract depends on unfinished function f"): fill or write `f` first |
| `vreact synth` on a `/** @trusted */` function or a component | refused (Lean checks nothing in a trusted body): remove `@trusted` / move the expression into a model function |
| a reducer over a discriminated union calling `@opaque` model functions | supported (contracts are instantiated inside the `switch` arms) |
| invariants about sums (`reduce`) under filter/map | provable, but needs a Lean lemma in `proofs/` (automation handles append, filter, map, `slice`, `toSorted`, `toReversed`, `with` (also swaps `xs.with(i, xs[j]).with(j, xs[i])`), `indexOf`/`findIndex` ranges, `range`, membership, `distinct`, concatenation of string literals, and counts `xs.filter(p).length` under append, delete-by-id, map-updates and mark-all) |
