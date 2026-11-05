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

The tsconfig needs `"strict": true` and `"lib": ["ES2023", "DOM"]` (for
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

Not supported: `any`, generics, classes, `Map/Set/Record`, recursive types,
non-discriminated unions (`string | number`), `ReactNode`/`children` props.

## Expressions

* Arithmetic `+ - *` on `int`; `/` produces `number`; use `idiv(a, b)` or
  `Math.floor(a / b)` for integer division (obligation: `b !== 0`); `%` (obligation).
* Comparisons `< <= > >= === !==`. `===` on objects/arrays is rejected (identity);
  compare keys/fields. `== null` / `!= null` allowed.
* `&& || ! ?: ?? ?.` and template literals.
* `xs[i]` (obligation: `0 <= i < xs.length`), `t[0]` on tuples, `x!` (obligation).
* Arrays: `length map filter some every find findIndex includes indexOf slice
  concat join reduce(f, init) toSorted(cmp) toReversed with at flatMap`, spread.
  Lambdas inline: `xs.filter((x) => x.id !== id)`.
* Strings: `length trim includes startsWith endsWith slice repeat toLowerCase
  toUpperCase` — exact UTF-16 semantics (case mapping is opaque to proofs).
* `Math.max/min/abs/sign/floor/trunc/round/ceil`, `String(x)`.
* Calls to verified top-level functions (their `requires` become obligations)
  and to local helper arrows (inlined).
* Narrowing: `x !== null`, `x.kind === "add"`, `switch (x.kind)`, early returns —
  fields of the narrowed variant become available, also inside handlers created there.

## Statements

`const`, `let` + reassignment (locals only), `if/else`, `return`, `switch`
(cases end with `return`/`break`, no fall-through), `for (const x of xs)` (may
assign outer `let`s; no `break`/`return` inside), `throw` (must be provably
unreachable), `assert(c)`, `assume(c)`. No `while`, `try`, `var`, recursion.

## Contracts

```ts
export function f(x: int, xs: readonly int[]): int {
  requires(0 <= x && x < xs.length);          // first statements
  ensures((r: int) => r >= 0);                // annotate the result type
  …
}
/** @opaque */  …   // callers see only requires/ensures
/** @trusted */ …   // body not verified, contract assumed (reported)
```

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

## Components

Order inside the body:

1. `requires(…)` — props precondition (what every parent must establish);
2. `callbackRequires(props.cb, (args) => …)` — what this component guarantees
   about the arguments it passes to callback props (the parent may rely on it);
3. hooks: `const [x, setX] = useState<T>(init)`, `const [s, dispatch] =
   useReducer(reducer, init)`, `useEffect(() => {…}, [deps])`,
   `useMemo(() => v, [deps])`, `useCallback(fn, [deps])` — top level,
   unconditional, before any early return;
4. `invariant(…)` — over props and state;
5. render-local `const`s, helper arrows, handlers;
6. `return <JSX/>` (early returns allowed).

Props: a single parameter `props: P` (or destructured `{ a, b }: P`) where `P`
is a record whose function-typed fields are callbacks (`=> void`, required).

Handlers (`onClick`, `onChange`, `onSubmit`, `onKeyDown`, …): arrow functions or
local closures; the event parameter supports `e.target.value`,
`e.target.checked`, `e.key`, `e.preventDefault()`. Setters, `dispatch`, at most
one parent callback per path. Continuous events (`onMouseMove`, `onScroll`, …)
must be robust and may not call parent callbacks.

Effects: setters and timers (`setTimeout`/`setInterval` callbacks become tasks),
external writes (`localStorage.setItem`, `document.title = …`, `console.*`) are
allowed and have no modelled effect; cleanups may not set state; no async.

JSX: intrinsic elements with string/int/bool/enum attributes (`className`,
`value`, `checked`, `disabled`, `placeholder`, `type`, …; no `style`, `ref`,
spread), child components with all their props, `{cond && <X/>}`, ternaries,
`xs.map(x => <El key={…}/>)` (keys `int` or `string`, distinct), text from
strings/ints/enums. `children` props are not supported yet. An element with a
handler may not contain an element with the same handler or a user component.

## Not yet supported (workarounds)

| feature | workaround |
|---------|-----------|
| `useRef`, `useContext`, custom hooks | lift state up / pass props; inline hook calls |
| `children` / `ReactNode` props | compose in the parent |
| recursion, `while` | `for…of`, array methods |
| generics | monomorphic helpers |
| `async`, fetch | keep I/O in an unverified module that calls verified reducers |
| guarded updates in `vreact synth` | write the guard by hand; synth fills straight-line code |
| a reducer over a discriminated union calling `@opaque` model functions | supported (contracts are instantiated inside the `switch` arms) |
| invariants about sums (`reduce`) under filter/map | provable, but needs a Lean lemma in `proofs/` (automation handles append, filter, map, membership, `distinct`, counts via `length`) |
