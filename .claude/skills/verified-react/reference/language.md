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
`.ts`/`.tsx`, characters other than letters, digits and `_` replaced by `_`; a
path segment starting with a digit or `_` gets a leading `M` (`src/_util.ts` is
`VTS.M_util`: Lean gives `_`-names meanings), and one that is a Lean keyword or
Lean name a trailing `_` (`src/end.ts` is `VTS.end_`). A file directly in `src`
named `Base` (in any letter case) is `VTS.Base_`, so its lemma file is
`proofs/Base_.lean`: `proofs/Base.lean` is the global lemma file (see
obligations.md). Two files that map to the same module, or to names differing
only in letter case, are rejected (`module name clash`): e.g. `limits.ts` +
`limits.tsx`, `my-x.ts` + `my_x.ts`, `todo.ts` + `Todo.tsx`, `end.ts` +
`end_.ts`. Rename one of them. Within a module, types and values share Lean's
one namespace: a function, component or constant named like a type of its
module (`type Limits = …; const Limits: Limits = …`, `type Todo = …; function
Todo(…)`) is rejected. Inline object and union types are named by the
translator after where they occur (`const config: { … }` → `Config`, a
function's result → `<Fn>Result`), with a subscript (`Config₂`) when that name
is taken by a type, function, component or constant of the module.

The tsconfig needs `"strict": true` (with every check of the strict family:
`strictNullChecks`, `noImplicitAny`, `strictFunctionTypes`, … none set to false)
and `"lib": ["ES2023", "DOM"]` (for `toSorted`/`toReversed`/`with`); without a
tsconfig, vreact uses these defaults. JSX is React's automatic runtime:
`"jsx": "react-jsx"` (or `"react-jsxdev"`), no `jsxImportSource` other than
`"react"`, no `jsxFactory`/`jsxFragmentFactory`/`reactNamespace`,
`react/jsx-runtime` resolving to React's installed package (not redirected by
`"paths"`/`"baseUrl"`), and no JSX pragmas (`@jsx`, `@jsxImportSource`,
`@jsxFrag`, `@jsxRuntime`, in any comment and any letter case) in a verified file.
Compiler options are a whitelist: the usual language, module, strictness, emit
and output options are accepted; options that switch checks off (`"noCheck"`,
`"noLib"`, `"noResolve"`, the removed `suppress…` options, `"resolvePackageJson…":
false`) and any option vreact does not know (newer ones) are rejected with the
option's name. The tsconfig.json read is the one in the project
root; a `tsconfig.json` inside the source directories is rejected (the bundler
compiles a file with the nearest one's settings, e.g. its `jsxImportSource`).

## Types

| write                                   | notes |
|-----------------------------------------|-------|
| `boolean`, `string`, `int`              | `int` = integers (`import { type int } from "vreact/spec"`) |
| `number`                                | IEEE float: allowed, but opaque — proofs know nothing about numbers (no arithmetic facts, `===` is an uninterpreted IEEE test); a division needs a divisor that is not zero |
| `"a" \| "b" \| "c"`                     | string-literal enums (`switch` on them is exhaustive) |
| `{ readonly f: T; g?: U }`              | records (optional field = `U \| undefined`) |
| `{ kind: "x"; … } \| { kind: "y"; … }`  | discriminated unions — any common string-literal field works |
| `readonly T[]`, `T \| null`, `[A, B]`   | lists, options (not both null and undefined), tuples (fixed length, at least one element; named members `[lo: A, hi: B]` too, but no optional `a?: A` or rest `...r: A[]` members) |
| `ReadonlyMap<K, V>`, `ReadonlySet<T>`   | Maps and Sets (also `Map`/`Set`): see [Map and Set](#map-and-set) |
| `(a: A) => void`                        | only as callback **props** (a direct field of a props type); never data: not a function's parameter or result, state, a constant, a local, a hole, an array element |

Not supported: `any`, generic types (generic type aliases and interfaces; generic
*functions* are, see Generics), classes, `Record`, `WeakMap`/`WeakSet`, recursive types,
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
  An `int` with a `number` (`i < xs.length / 2`, `i * 0.5`, either order) is widened
  to a `number`, as in JS.
  Unary `+` only on numbers (`+s` on a string is rejected: ToNumber is not modelled).
* `a / b` (a `number`) has the obligation that the divisor is not zero, unless it is
  a nonzero literal (`x / 2`, `x / -0.5`, or a `const` initialised with one): VTS
  values are JS values up to the sign of zero (an int that is 0 may be `-0` in JS:
  `-x`, `a * b`, `a % b`, `Math.trunc(a / b)` give `-0`), and only a division by a
  zero tells the two apart (`1 / 0` is `Infinity`, `1 / -0` is `-Infinity`). Prove it
  with `requires(b !== 0)` (or `b > 0` for an int) or a guard
  `b === 0 ? … : a / b`; for a `number` divisor only `b !== 0` / `b === 0` help
  (nothing relates `<` and `===` on numbers).
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
  type to have TypeScript check it. Its nullish value is known through fields, indexes,
  `!`, optional chains and the reads of a Map, Set or array (`r.get(k)?.name === x`,
  `r.at(0)?.id === y`); a comparison it cannot type asks for the annotation.
* `+` with a string operand concatenates; `int`, `boolean` and enum operands are
  converted as in template literals (`x + "px"`); a `number` or nullable operand is
  rejected (use an int, or `${n}`). Bitwise operators (`~ & | ^ << >> >>>`) and
  compound assignments other than `+=`/`-=` are rejected.
* Widening as in TypeScript: an `int[]` where `(int | null)[]` is expected
  (elementwise, also in a spread), an enum member where a `string` is expected
  (`return k;`, `k === s`). A conditional or an array literal without an expected
  type covers all its branches or elements: `c ? i : 0.5` and `[i, 2.5]` are numbers,
  `c ? color : "other"` and `[color, "other"]` strings (`c ? color : "red"` stays a
  `Color`); the others take the first one's type when it covers them (`c ? xs : []`).
  An unannotated top-level `const` takes a numeric, string or boolean literal, typed
  by its value (`const N = 3` is an `int`, `-2.5` and `1e400` (Infinity) are numbers);
  annotate any other initialiser. The same inline object type or string-literal union
  in one module is one type (e.g. `hole<{ readonly v: int }>()` returned from a
  function declared to return `{ readonly v: int }`).
* `&& || ! ?: ?? ?.` (also `a ?? b ?? 0`) and template literals. `?.` skips the whole rest
  of the chain, as in JS: `x?.tags.length ?? 0`, `m.get(k)?.has(id) ?? false`,
  `grid.get(r)?.get(c) ?? 0`, `xs?.[0]` (optional calls `f?.()` are rejected).
* `xs[i]` (obligation: `0 <= i < xs.length`), `t[0]` on tuples, `x!` (obligation).
  `xs.with(i, v)`: obligation `0 <= i < xs.length`; a negative index counts from the end
  when written `-k` (`xs.with(-1, v)` writes the last element; obligation `0 < k <=
  xs.length`), any other index must be non-negative (VTS's restriction).
* Arrays: `length map filter some every find findIndex includes indexOf slice
  concat join reduce(f, init) toSorted(cmp) toReversed with at flatMap`, spread.
  Lambdas inline: `xs.filter((x) => x.id !== id)` (they may ignore parameters:
  `xs.map(() => "")`). Callbacks take the element only (and `reduce`'s the accumulator and
  the element), except `map`, which may take the index (`xs.map((x, i) => …)`): a condition
  on positions is `forall(0, xs.length, (i) => … xs[i] …)` (e.g. `a.length === b.length &&
  forall(0, a.length, (i) => a[i] === b[i])`). Exact arities: optional arguments that are not modelled
  are rejected (`thisArg`; `includes(v, fromIndex)` → `xs.slice(k).includes(v)`;
  `indexOf(v, fromIndex)`). `includes`, `indexOf` and `distinct(xs)` without a
  key need primitive elements (`boolean`, `int`, `string`, enums, options of
  them): on records/arrays/tuples JS compares identity (use `some`/a key), on
  `number` SameValueZero. Searching for the nullish value, `xs.includes(null)` /
  `xs.indexOf(undefined)` on optional elements, works for every element type
  (a present value is never null). `find`/`at` on arrays of optional values are rejected
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
* `Math.max/min/abs/sign/floor/trunc/round/ceil`, `String(x)`. On ints they are exact
  (`Math.floor(a / b)` and `idiv` are integer division); on numbers they are opaque,
  like every number operation: a contract about numbers is provable only by
  congruence (`r === (a / b < 0.5)` for `return a / b < 0.5`), never by computing.
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

## Map and Set

`ReadonlyMap<K, V>`, `ReadonlySet<T>` (and `Map`, `Set`: prefer the readonly forms in
signatures, state and props, so that TypeScript rejects `set` on them), wherever a type may
appear: parameters, results, state, props, record fields, array elements, reducer state.

* Keys and elements: `int`, `string`, `boolean`, string-literal enums. JS compares keys with
  SameValueZero, so `number` (NaN, -0), objects, arrays and tuples (identity) and optional
  types (`null` and `undefined` are different keys) are rejected. Values: any data type but an
  optional one (`m.get(k)` is `undefined` for a missing key): no `ReadonlyMap<K, V | null>` —
  delete the key instead. In a generic function (see Generics), a key or element may be a type
  parameter with an equality constraint (`ReadonlySet<K>` with `K extends int | string`), and a
  value any type parameter (`ReadonlyMap<K, V>`, `ReadonlyMap<K, readonly V[]>`); a key of an
  unconstrained or field-constrained type parameter is rejected ("a Map key needs equality":
  constrain `K`, or key by a field, `ReadonlyMap<int, T>`).
* Order is JS's insertion order, exactly: `set` on a present key keeps its position, on a new
  key appends it; `delete` then `set` moves the key to the end; `new Map(entries)` with a
  repeated key keeps its first position and its last value; `new Set(xs)` keeps first occurrences.
* Create: `new Map<K, V>()`, or `new Map()` where the type is known (an annotation,
  `useState<T>(…)`, a parameter, the return type) — never with neither (TypeScript types it
  `Map<any, any>`); `new Map(m)` (a copy), `new Map(pairs)` (`[k, v]` pairs: a literal,
  `new Map<int, Item>(xs.map((x: Item) => [x.id, x]))`), `new Set(xs)`, `new Set(s)`. A
  literal of pairs needs no type arguments: its types are those of its first pair
  (`new Map([["a", 1]])` is a `Map<string, int>`); pairs computed by a callback do
  (`new Map<int, Item>(…)`: TypeScript infers `number` for an integer, which cannot tell `int`
  from `number`). `new Set(string)` is rejected (it iterates code points).
* Read: `m.get(k)` (`V | undefined`: `m.get(k) ?? d`, `m.get(k)?.f`, `m.get(k)!` with an
  obligation, or `const v = m.get(k); if (v !== undefined) …` — a call is not narrowed),
  `m.has(k)`, `m.size`, `s.has(x)`, `s.size`.
* Iterate where the iteration is consumed at once: `[...m]` / `[...m.entries()]` (`[k, v]`
  pairs), `[...m.keys()]`, `[...m.values()]`, `[...s]`, `Array.from(it)` (one argument),
  `for (const [k, v] of m)`, `for (const k of m.keys())`, `for (const x of s)`, and the argument
  of `new Map(…)` / `new Set(…)` — also `m.get(k) ?? fallback` for a Map of Maps or Sets
  (`new Set(m.get(k) ?? [])` is a copy of the stored Set, or an empty one; kept as a value, write
  `m.get(k) ?? new Set<E>()`). An iterator anywhere else (stored in a `const`, passed,
  rendered) is rejected: a JS iterator is used up once and sees later changes. Render a Map as
  a keyed list: `{[...m.values()].map((it) => <li key={it.id}>…</li>)}`.
* Tuples destructure by position: `([k, v]) => …`, `for (const [k, v] of m)`, `const [k, v] = pair`;
  `[, v]` skips an element, and a shorter pattern binds a prefix, as in JS (`([k]) => k`,
  `toSorted(([a], [b]) => a - b)`). A pattern longer than the tuple is rejected.
* Update in an expression with `.set` / `.add` chains on a fresh copy:
  `new Map(m).set(k, v)`, `new Set(s).add(x).add(y)`. As statements, mutate a local copy:
  `const n = new Map(m); n.set(k, v); n.delete(j); n.clear(); return n;` — only a `const`
  initialised in the same function with `new Map(…)` / `new Set(…)`, also in a `for…of`
  (`for (const x of xs) n.set(x.id, x);`), a functional update
  (`setM((p) => { const n = new Map(p); n.set(k, v); return n; })`) or a reducer. Rejected:
  mutating parameters, props, state, constants, `let`s or values read from elsewhere (the
  caller, React or other code holds the same object); `set`/`add`/`delete`/`clear` inside an
  expression (`if (n.delete(k))`, `console.log(m.set(…))`); mutating from inside a callback or
  helper; using `n` — storing it, passing it to a function, setter or child, rendering it,
  capturing it in a handler or helper — when a mutation of `n` follows (later in the code, or in
  a later loop iteration; the function's own `return n` is fine, a callback's `return n` is
  not — it hands `n` back to the function, which goes on): mutate first, or pass a copy
  `new Map(n)`; mutating `n` in a `for…of` over `n` itself (iterate `[...n]`). Logging or
  writing out `n` where it stands is not a use: `console.log("start", n)`,
  `localStorage.setItem(k, JSON.stringify(n))` (the model reads nothing of it). A local named
  like a global (`const console = new Set(…)`) is an ordinary variable: `console.add(1)` mutates
  it. The mutating
  methods are only called directly, `n.set(…)`: not through an index (`m["clear"]()`), as a
  value (`const f = n.set`, `n.set.bind(n)`) or via the prototype (`Map.prototype.set.call(m, …)`),
  and a Map or Set is never indexed (`m[k]`: use `m.get(k)`).
* Not supported: `===` on Maps/Sets (identity: compare the contents; also in generic code),
  truthiness (`if (m)` is always true: test `m.size > 0`), `forEach` (use `for…of`), `entries()`
  of a Set, `WeakMap`, `WeakSet`, `Map.groupBy`, the ES2025 Set methods, a Map or Set as a JSX
  child or a string, covariance (TypeScript passes a `ReadonlyMap<int, int>` where a
  `ReadonlyMap<int, number>` or a `ReadonlyMap<K, V>` with `V = number` is expected, and a
  `ReadonlySet<Color>` as a `ReadonlySet<string>`; in VTS the key, value and element types must
  be the same). Effect dependencies compare Maps by identity (a new Map re-runs the effect).
* Contracts use the same forms: `r.get(k) === v`, `r.has(k)`, `r.size`,
  `[...r.values()].every((v) => v >= 0)`, frames
  `[...m.keys()].every((j) => j === k || r.get(j) === m.get(j))`, order
  `[...r.keys()].indexOf(k) === m.size`. The automation knows `get`/`has`/`size` after
  `set`/`delete`, that keys are distinct (keyed lists by the keys, or by the values' `id` when an
  invariant states `[...m.entries()].every(([k, v]) => k === v.id)`), that a value read with
  `m.get(k)` is the value of `k`'s entry (so such an invariant applies to it), the position of a
  set or re-set key, the entries and values of `new Map(pairs)`, of `new Map` of a filtered
  `[...m]` and of the loops `for (const x of xs) n.set(f(x), g(x))` / `n.add(f(x))` / `n.add(x)` (they come
  from the pairs), `new Map`/`new Set` of literals, `[...m].length === m.size` (also
  `[...m.values()]`), `new Set(xs).size <= xs.length` (`===` when `distinct(xs)`), the size of
  `new Map(pairs)` with distinct keys, and membership in a Set after `add`/`delete` (also a Set
  stored in a Map). Other loops (a loop of `delete`s, a sum over `m.values()`) need a lemma, as
  for arrays. It also knows that an index `new Map(xs.map((x) => [x.id, x]))` (or the loop
  `for (const x of xs) n.set(x.id, x)` from an empty `n`) maps each element's id to that
  element under `distinct(xs, (x) => x.id)`, and pigeonhole on distinct elements: a Set whose
  members are all in `b` is no larger than `b`, and with equal sizes the inclusion goes both
  ways (`a.size === b.size && [...a].every((x) => b.has(x))` means the same members; likewise
  for Map keys). Lean lemmas for `proofs/` (e.g. `JSMap.keys_set`, `JSMap.get_set`,
  `JSMap.entries_set`, `JSMap.mem_entries_of_get`) are in `VReact/JSMap.lean`.

## Statements

`const`, `let` + reassignment (locals only), `if/else`, `return`, `switch`
(cases end with `return`/`break`, also `case "x": { …; break; }`; no fall-through;
`default` anywhere, also grouped `case "a": default:`; on an int/string/boolean/number:
literal, negated-literal or constant labels compared with `===`, a non-integer label
on an int is rejected; on an enum or `x.kind`: string literals), `for (const x of xs)` (may
assign outer `let`s; no `return`/`continue` inside, `break` only to end a `switch`
case), `throw` (must be provably
unreachable), `assert(c)`, `assume(c)`. No `while`, `try`, `var`, recursion.
Code after a `return` in the same block never runs and is rejected (in functions,
components, handlers, effects, timer callbacks). Async functions and generators
are rejected everywhere (an async predicate returns a promise, which is always
truthy; calling a generator does not run its body).

`assume(c)` is a trusted fact (reported `ASSUMES`): that `c` holds whenever control
reaches it, for every input the enclosing function's `requires` (a component's
precondition and invariant) allow — not only the inputs the program passes. Lean
keeps it in exactly that form (the precondition and the path to it as hypotheses;
a user proof may use it). Not in generic functions (see Generics), nor inside a
`for…of` body, an array-method callback or a functional update `setX((p) => …)`:
Lean checks those for every value of the loop's variables, the element or the
state, so the fact would be assumed for all of them — use `assert(…)`, or
`requires(…)` of a helper function that takes the values as parameters.

A Map or Set mutated by statements follows the rules of [Map and Set](#map-and-set).

Closures and `let`: JS closures read a variable when they run. So a function
that runs later (helper arrow, handler, callback prop, `setX(prev => …)`, effect,
timer, cleanup, `useCallback`) may not read a `let` that is reassigned after the
function is created — copy it first: `const capNow = cap;`. No function or
callback (array callbacks included) may assign a `let` declared outside it —
use `for…of` or `reduce`. Array callbacks may read outer `let`s. This holds
wherever code is translated: also in contracts, constant initialisers and
`assert(…)` facts, and in the contracts and initial state of a `@trusted`
declaration (its body is not checked).

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

Callers of an `@opaque` function get its `ensures` instantiated at each call, also at a call
under a binder (in a timer callback or a functional update, a continuous or rebased handler,
a `map`/`every` lambda); not at a call that occurs only inside a quantified hypothesis (an
`invariant` such as `xs.every((x) => f(x) > 0)`), which the automation instantiates itself
without the contract: state what is needed there directly.

Several `requires` form one precondition, in order: a later one may rely on an
earlier one (`requires(xs.length > 0); requires(xs[0] >= 0)`); the same holds for
a component's `requires` and `invariant`s. A reducer's `requires` may mention
only the action (React may apply a queued action to any state): it becomes a
`precondition` obligation at every `dispatch(…)`. Inside contracts,
guards are in scope as JS evaluates them: the right side of `&&` / `||`, the
branches of `?:`, and quantifier bodies
(`forall(0, xs.length, (i) => xs[i] >= 0)`, `xs.every((r) => r[0] > 0)`) may index
under their guard. Only `xs.every`/`xs.some` with `(x) => condition` and
`forall`/`exists` with `(i) => condition` (an expression body) are such quantifiers;
another callback (`(x) => { …; return c; }`, `function (x) { … }`) is read as code,
as in a handler (where `implies(a, b)` evaluates both arguments).

`implies(a, b)` is a function call, so JS evaluates `b` even when `a` is false. The
arguments of `requires`, `invariant`, `assert`, `assume` and a module-level
`assert` are evaluated at every call, render, dispatch or module load (also with
contract checking off), so there `b` must be safe on its own: its indexes, `!`s,
divisors and callee preconditions are checked without `a`
(`requires(implies(xs.length > 0, xs[0] >= 0))` fails its `index` obligation:
`xs[0]` of `[]` is read). Write
`!a || b` instead (`xs.length === 0 || xs[0] >= 0`, `x === null || x.v > 0`), which
guards and narrows as JS evaluates it. Only in an `ensures` lambda and in the
expression body of a `callbackRequires` lambda, which the app never calls, does `b`
see `a` as its guard (`ensures((r: int) => implies(xs.length > 0, r === xs[0]))`).
`vreact synth`'s random tests, which do call an `ensures` lambda, evaluate such an
`implies(a, b)` as `!a || b` (`b` only where `a` holds), as the prover reads it; an
`implies` in code inside the lambda (a `filter` callback, an operand of `===`)
evaluates both arguments, there as in Lean.

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

## Generics

```ts
export function firstOr<T>(xs: readonly T[], d: T): T { … }                        // no constraint
export function countKey<K extends int | string>(xs: readonly K[], k: K): int { … } // equality
export function byId<T extends { readonly id: int }>(xs: readonly T[], id: int): T | undefined { … } // fields
```

Top-level functions may have type parameters (exported or not, also `@opaque`;
not `@trusted`: Lean would assume a trusted generic function's type and
contracts for every type, also empty ones and ones with values JS never passes —
stronger than its JS meaning, and possibly contradictory; verify it, or write one
`@trusted` function per concrete type). For the same reason a generic function's
body may not `assume(…)` (Lean keeps an assumed fact as a theorem about the
function's parameters, here for every type: `assume(a === b || b === c || a === c)`
under `K extends boolean` would be false at `Int`): state the fact as `requires(…)`,
which each caller proves (or assumes) at its own types, or prove it with
`assert(…)`. A type parameter may appear in parameter and return types,
local annotations (also of helper arrows and callback parameters), `hole<T>()`,
arrays, `T | null`, tuples and Map and Set types (`ReadonlyMap<K, V>`,
`ReadonlySet<K>`, `ReadonlyMap<K, readonly V[]>`, `new Map<K, V>()`, `new Set(xs)`;
a Map key or Set element only under an equality constraint, see below and Map
and Set) — not inside object types (`{ readonly v: T }`: pass the value as its
own parameter). At most one constraint per parameter:

* **none** — values of `T` are abstract: they can be passed, stored (arrays,
  `T | null`, tuples), returned, given to other generic functions, and used with
  the array methods that do not compare elements (`map filter some every find
  findIndex slice concat toReversed toSorted(cmp) with at reduce flatMap`,
  `length`, spread, indexing).
* **equality** — `K extends int | string | boolean | "a" | Color` (unions of
  these; `Color` a string-literal enum type): also `===`/`!==` on `K`,
  `includes`, `indexOf`, `distinct(xs)` and `distinct(xs, x => k)` with a `K` key,
  and `K` as a Map key or Set element (`ReadonlySet<K>`, `ReadonlyMap<K, V>`;
  Lean `JSSet K` / `JSMap K V` with `[DecidableEq K]`).
  `K extends number` is rejected (`NaN !== NaN`; use `int`).
* **fields** — `T extends { readonly id: int; readonly note?: string }` (or the
  name of a record type): `x.id` on `x: T` (an optional field is `U | undefined`).
  Field types may not mention type parameters. Equality and fields cannot be
  combined (no intersections).

Map and Set code in a generic body is the same as elsewhere: copies and fresh
locals (`const n = new Set(s); if (n.has(k)) n.delete(k); else n.add(k); return
n;`), `for (const [k, v] of m)`, spreads, `m.get(k) ?? d`, and `m.get(k) === v`
when `V` has an equality constraint (never `===` on the Maps or Sets themselves).
A helper such as `toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K)` is
proved once and used at `int` and `string` keys, in functions and in a
component's functional updates (`setSel((s) => toggleIn(s, id))`).

Even under `T extends int` or `T extends string` the values of `T` are abstract:
no arithmetic, ordering, `Math.*`, string conversion (`${x}`, `+`), string
properties or methods, truthiness (`if (x)`, `x ? … : …`, `!x`, `xs.filter((x) =>
x)`, also under `K extends boolean`), comparison with a value of another type, and
no object literal of type `T` (the body is checked once, for every type `T` may
be). A generic helper cannot take a callback (`p: (x: T) => boolean`): read a
property through a field constraint (`T extends { readonly done: boolean }`), or
write the arrow at the call site. Null tests on `T | null`
work (a type parameter is never instantiated with a nullable type).

Calls infer the type arguments from the VTS types of the arguments (where
TypeScript cannot tell `int` from `number`: `count(xs, 1.5)` instantiates
`number`), also through arrays, tuples and Map and Set types (`keysOf(m)` with
`m: ReadonlyMap<int, Order>` gives `K = int`, `V = Order`), then from the type the
result must have (`const xs: readonly int[] = emptyOf()`, `const e:
ReadonlyMap<int, string> = emptyMap()`), then for `[]`, `null` and literals; two
arguments of `int` and `number` give `number`, an enum and a `string` give
`string` (a Map or Set argument must then have exactly the instantiated type: no
covariance). Otherwise write the
type arguments (`emptyOf<int>()`; "cannot infer T"; an argument that cannot be
typed reports its own error instead). Each call is checked: an
instantiation is never nullable (`firstOr(xs, null)` with `xs: (int | null)[]` is
rejected — give the function a `T | null` parameter instead), never `number` for
an equality constraint (`toggleIn(s, 1.5)` with `s: ReadonlySet<int>` is
rejected), and for a field constraint is a record (or a union, in
every variant, or another type parameter with that field) whose field has exactly
the constraint's type and the same `null`/`undefined`. An argument for a parameter
`T | null` must be `null` (not `undefined`) when absent, as the declared type says
(TypeScript would absorb `undefined` into `T`); likewise for `T | undefined`, also
inside arrays, tuples and Map values (`ReadonlyMap<int, readonly (V | null)[]>`).

A generic function is proved once for every instantiation, and its `ensures`
hold for every type: a contract that is true only at the module's own calls is
not proved. Callers of an `@opaque` generic function reason with these contracts
at whatever type they call it (also at their own type parameters).

Rejected: generic type aliases and interfaces, generic components, generic
reducers (`useReducer`), generic arrow functions, function expressions and
function types, `@trusted` generic functions, `assume(…)` in a generic function, default type arguments (`<T =
int>`), `const` type parameters, other constraints (`unknown`, `any`, `object`,
`keyof`, unions of object types, intersections, constraints mentioning a type
parameter), a Map key or Set element of a type parameter without an equality
constraint (`ReadonlySet<T>` with `T` unconstrained, `T extends {}` or a field
constraint: JS would compare objects by identity), recursion.

`vreact synth` tests a generic function with `int` and `string` values for an
unconstrained or equality-constrained type parameter (they stand for every type,
or every type with equality: the body cannot tell which; Maps and Sets of them are
random JS Maps and Sets with distinct keys, printed as `{"Map":[[k, v], …]}` /
`{"Set":[…]}` in counterexamples) and with a witness record
for a field constraint (the constrained fields, an optional one absent as
`undefined`, and one more field); Lean proves the fill once for every
instantiation. Generic helpers of the module are offered as calls at the hole's
types (when the arguments determine every type parameter), and `xs.filter((x) =>
x.f !== v)` also for elements of a field-constrained type parameter.

## Components

Order inside the body:

1. `requires(…)` — props precondition (what every parent must establish);
2. `callbackRequires(props.cb, (args) => …)` — what this component guarantees
   about the arguments it passes to callback props (the parent may rely on it;
   several for one callback are conjoined). JS evaluates the first argument at
   every render: it is `props.cb` on the props parameter or a name destructured
   from the props parameter, and the contract is the prop's that name holds
   (`{ cb: f }` then `callbackRequires(f, …)` is cb's), never one spelled like it;
   anything else is rejected. The body is a contract (guards in scope, as below in
   Contracts: `implies(a, b)` may index under `a`); a block body is read as code;
3. hooks: `const [x, setX] = useState<T>(init)`, `const [s, dispatch] =
   useReducer(reducer, init)`, `useEffect(() => {…}, [deps])`,
   `useMemo(() => v, [deps])`, `useCallback(fn, [deps])` — top level,
   unconditional, before any `if`/`switch`/early return (never in branches,
   loops, handlers or closures; parentheses around the call do not matter); deps
   exhaustive (`{ x }` reads `x`). Deps are data paths: variables, fields
   (`item.count`, `props.item?.count`), `length`, `size`. A call `m.has(k)` reads
   `m` and `k`: list `m` (or a prefix of a field path), never the method —
   `[m.has]`, `[xs.slice]`, `[s.trim]` are rejected (the same function for every
   receiver: React would never recompute), and so are library constants
   (`[Number.MAX_SAFE_INTEGER]`) and a tuple's `length` (list the tuple). Values
   from outside the component (`Math`, imports, top-level consts) are never
   needed: leave them out. An effect may also list a setter or `dispatch`, or a
   top-level function, const or component (or an import of one), which never
   change; a local helper arrow or a JSX const (new each render: the effect runs
   after every render); or a `useCallback` function (changes when its own deps
   do); not a parent callback, nor `props` itself (list its fields), nor a global
   such as `Math` (leave it out), also through a `useCallback` it lists. An
   initial value may read the props, the state
   declared before it and top-level declarations (not render locals): React uses
   it at mount, when that state has its own initial value (`useState(a)` starts
   at `a`'s initial value), but evaluates a non-lazy one at every render, so it
   is also checked with each render's state (`useState(10 % a)` needs `a !== 0`
   in every state; the lazy `useState(() => 10 % a)` runs at mount only). Other
   hooks (`useLayoutEffect`, `useRef`, …) are not modelled, and a hook other than
   `useEffect` called as a statement (its value unused) is rejected;
4. `invariant(…)` — over props, state and top-level declarations (a
   `requires`: props and top-level declarations only; neither may read render
   locals);
5. render-local `const`s, helper arrows, handlers. A local arrow function is
   translated where it is called or attached as a handler, so it may read a
   `const` (or a `let` nothing assigns) declared after it, as long as that use
   comes after the declaration (`const inc = () => setN(n + step); const step:
   int = 2; … onClick={inc}`; calling it in the render before `const step` reads
   `step` in its temporal dead zone, a ReferenceError: rejected, and so is
   attaching it in a JSX const declared before `step`). A `useEffect`,
   `useCallback` or `useMemo` function may not read a local declared after the
   hook call: the dependency array cannot list it (temporal dead zone), so React
   would keep a stale function (the `useMemo` function runs at the call: a
   ReferenceError);
6. `return <JSX/>` (early returns allowed).

Props: a single parameter `props: P` (or destructured `{ a, b }: P`) where `P`
is a record whose function-typed fields are callbacks (`=> void`, required).
`key`, `ref`, `__self` and `__source` are not props: React 18 never passes them
to the component (`props.key` is undefined; the development JSX transform uses
`__self` and `__source`), so `P` may not have fields with these names (however
spelled: `key`, `"key"`, `["key"]`), `ref={…}` is rejected (refs are not
modelled), and so are `__self=…` / `__source=…`. In any record type, a field
written as a string or a computed string (`"b": int`, `["c"]: int`) is the
property `b` (`c`) everywhere:
`r.b`, `{ b: 1 }`, `{ "b": z } = r`; other computed names are rejected.

Parameters are bound to arguments by position, so functions VTS translates
(components, callbacks, handlers, array callbacks, local helpers, top-level
functions) may not have a `this` parameter (`function (this: T, x) …`: it types the
receiver, `x` is the first argument), a rest parameter, a default value or an
optional parameter. A DOM handler's one parameter is the event: `(e) => …`, never
`(...e) => …` (`e` would be the array `[event]`, `e.key` undefined).

Handlers (`onClick`, `onChange`, `onSubmit`, `onKeyDown`, …): arrow functions or
local closures; the event parameter supports `e.target.value`,
`e.target.checked`, `e.key`, `e.preventDefault()` (also `e.currentTarget.…`).
Which fields exist depends on the element and the handler prop the handler is
attached to, not on the type annotation of `e` (React's handler types are
bivariant: TypeScript accepts `(e: ChangeEvent<HTMLInputElement>) => …` on a
`<div>`): `e.currentTarget` is the element the handler is on, and its `value`
is a string only on `<input>`, `<select>`, `<textarea>`, `<button>`, `<option>`,
`<output>`, `<data>` (undefined on a `<div>`, a number on an `<li>` or
`<progress>`; HTML elements only, never inside `<svg>`), its `checked` only on `<input>`; `e.target` may be any element
inside the one the handler is on, so `e.target.…` is accepted only on an
`<input>`, a `<textarea>` and a `<select>`'s `onChange` (not its `onInput`: an
`input` event a script dispatches at an option reaches it with the option as
`e.target`; read `e.currentTarget.value`); `e.key` only
in `onKeyDown`/`onKeyUp`/`onKeyPress`. Read the event in the handler's own
statements (array callbacks there may too): a function created in the handler —
a functional update `setX(p => …)`, which React calls when it processes the
update and again when it rebases it, or a local helper — may run after the
event's dispatch, when `e.currentTarget` is null and `e.target.value` is the
element's value at that time. Copy it first: `const v = e.target.value;
setX((p) => … v …)`. Setters, `dispatch`, at most
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
`if (left <= 0) return; setTimeout(() => setLeft(left - 1), 1000)`, and read the
effect body's top-level `const`s declared before the registration, each bound to
its value (`const step: int = props.fast ? 2 : 1;
setInterval(() => setN((k) => k + step), 100)`) — but not the body's `let`s, a
Map or Set the body mutates, or a `const` whose value has proof obligations of its
own (`100 % props.d`: compute it in the callback); the delay is
checked where the timer is registered; no further `setTimeout` arguments),
external writes (`localStorage.setItem`, `document.title = …`, `console.*`) are
allowed and have no modelled effect, but JS evaluates their arguments, so these
are checked like any expression (here and in handlers, timers, cleanups, render
and functions: `console.log(xs[i].name)` needs `i` in bounds; an argument may be
`JSON.stringify(v)` or `JSON.stringify(v, null, 2)`, which cannot throw on a VTS
value; no casts, `eval`, `arguments`, `m["clear"]()`); no async. `console`,
`localStorage`, `document`, `setTimeout`, `clearTimeout`, … are the globals only: a local,
parameter or import with such a name is an ordinary variable (a parameter `document` has no
external `document.title`). A cleanup
is an inline `() => { … }`, returned at the end of the effect body or of a branch
of it, that only calls `clearTimeout`/`clearInterval` and makes those external
writes, possibly under `if`/`else` (`if (id !== null) clearInterval(id)`: a timer
handle is never null). A timer handle is `const id = setTimeout(…)` and can only be
cleared, by a cleanup returned after that statement: one returned earlier (from a
branch before it) would read `id` in its temporal dead zone, a ReferenceError
when React calls it. No setters, `dispatch`, parent callbacks or local helpers:
it runs later with the values it captured. Its conditions and arguments are
checked where the effect returns it, under the facts that hold there (the
effect's early returns, its `if`s). Statements after the effect's `return` are
rejected (they never run). A cleanup's arguments and conditions, and a timer's
delay, must also be data: they may call only the library's reading methods (array
methods but `push`/`pop`/`shift`/`unshift`/`splice`/`sort`/`reverse`/`fill`/
`copyWithin`, string and number methods, `Math.*`, `JSON.stringify`,
`m.get`/`has`/`keys`/`values`/`entries`), `String(…)` and the module's functions; a function
is only called there, never passed or stored (inline callbacks aside: `[1].map(setN)` and
`String({ toString: setN })` would run the setter); no mutators (`xs.push(1)`,
`m.get(k)!.push(x)`), `.call`/`.apply`/`.bind`, `new`, assignments.

JSX: intrinsic elements with string/int/bool/enum attributes (`className`,
`value`, `checked`, `disabled`, `placeholder`, `type`, …; no `style`, `ref`,
spread), child components with all their props, `{cond && <X/>}`, ternaries,
`xs.map(x => <El key={…}/>)` (keys `int`, `string` or a string-literal enum, distinct), text from
strings/ints/enums (booleans render nothing, but are checked). `key={…}` outside
lists is checked too (JS evaluates it), and the keys of the children of one element or
fragment must be distinct, compared as strings as React does (`key={1}` and `key="1"` are one
key): two children always present with the same written key (also a JSX const rendered twice)
are rejected, and otherwise, unless all keys are distinct strings, a `unique-keys` obligation
covers the keys of the children present (a conditional child under its condition). A keyed list
or a fragment is one child with keys of its own, so `<li key="head"/>` next to
`{xs.map((x) => <li key={x}/>)}` never collide. Give siblings keys with different literal
prefixes (`` key={`viewer-${id}`} ``, `` key={`notes-${id}`} ``): those are proved.
A JSX const (`const row = <p>{e}</p>;`) is checked where it is declared, even if it is
rendered only under a condition or not at all (JS evaluates it there); JSX only appears in a
component's render.
`children` props are not supported yet.
Tags are plain names: a lower-case one is always the HTML element (`<p>` even
where a variable `p` exists), a capitalised one a verified component. Rejected:
member-expression tags (`<props.as>`, `<ui.Button>`: a dynamic element type),
namespaced tags (`<svg:rect>`), custom elements (`<my-el>`) and `<script>`. An
HTML tag is ASCII lower-case letters and digits (the document lower-cases names:
`<bUTTON>` would be a `<button>`; `<foreignObject>` outside `<svg>` is rejected).
Inside `<svg>` (and `<math>`) React creates SVG (MathML) elements, except inside a
`<foreignObject>`, whose children are HTML again: there an `<input>`, `<button>`,
`<select>`, `<textarea>`, `<label>`, `<form>`, … is rejected (it would be an SVG
element with no value, type or activation), other elements count as plain content
for the layout checks below (an SVG `<a href>` does not stop a label), and user
components are rejected. React throws while rendering children of a void element
(`<input>`, `<br>`, `<hr>`, `<img>`, …, even `{false}`) and a `<textarea>` with
children: both are rejected (a textarea's text is `value`/`defaultValue`). A
`<select>` may contain only `<option>` and `<optgroup>` elements (and text), an
`<optgroup>` only `<option>`s, an `<option>` only text, as react-dom's
`validateDOMNesting` says (React only warns): no other element and no user
component there, also through a list, a condition or a JSX const. A control inside
a select would run the select's `onChange` (react-dom collects `onChange` from
the control that changed up to the root) and be its `e.target`. A `<datalist>`
may hold anything (its `<option>`s follow the same rule). Also
rejected: a `children=` attribute (it is the element's children), `contentEditable`
(the user could delete nodes React rendered: React's next update throws),
`suppressContentEditableWarning`, `is=` (a customized built-in element), a
`javascript:` URL written in `href`/`src`/`action`/`formAction`/`data`, `srcDoc`
(a same-origin document whose scripts reach this page), and
`value`/`defaultValue` other than `""` on an `<input>` that may be `type="file"`
(setting a file input's value throws): its `type` must be a string, a choice
between strings (`show ? "text" : "password"`) or an enum, without `"file"`.
Type keywords are matched ASCII-case-insensitively, as HTML does
(`type="CheckBox"` is a checkbox, `type="chec&#8490;box"` with a Kelvin sign is
not: a text input). Character
references in JSX text and attribute strings are decoded as JSX does (`&amp;`,
`&#65;`, `&#x41;`, the HTML 4 entities), also for the layout checks below:
`type="&#115;ubmit"` is a submit button. References that JSX compilers read
differently (`&check;` and other names outside HTML 4, `&#X41;`, `&#+65;`, code
points above U+10FFFF) are rejected: write the character, or `{"…"}`. So are JSX
text with a tab (Babel makes it a space) and attribute strings with a line break,
written as one or as a reference (`&#10;`): Babel replaces a line break and the
whitespace after it with a space; write `{"a\n b"}`.
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
| `useRef`, `useContext`, `useLayoutEffect` (its updates are synchronous, during the commit), custom hooks | lift state up / pass props; `useEffect`; inline hook calls |
| `children` / `ReactNode` props | compose in the parent |
| recursion, `while` | `for…of`, array methods |
| generic type aliases, interfaces, components, reducers and arrows | concrete types; generic top-level functions (see Generics) |
| a Map key / Set element of an unconstrained or field-constrained type parameter (`ReadonlySet<T>`, `ReadonlyMap<T, V>` with `T extends { readonly id: int }`) | constrain it (`K extends int \| string`), or key by a field (`ReadonlyMap<int, T>` with `x.id` as the key) |
| Map/Set covariance (`ReadonlyMap<int, int>` passed as `ReadonlyMap<int, number>`) | give the Maps / Sets the same key, value and element types |
| `@trusted` generic functions | verify the generic function (`@opaque` hides its body from callers), or one `@trusted` function per concrete type |
| callbacks as parameters of top-level functions (`p: (x: T) => boolean`), functions in state, locals, holes or arrays | write the arrow at the call site (`xs.find((x) => …)`); in a generic helper, read a property through a field constraint (`T extends { readonly done: boolean }`) |
| `async`, fetch | keep I/O in an unverified module that calls verified reducers |
| guarded updates in `vreact synth` | write the guard by hand with a hole per branch; synth fills straight-line code (all holes of a function are proved together; a hole per `case`/branch is searched once) |
| deleting from a Map or Set in `vreact synth` (its grammar only grows them: `new Map(m).set(k, v)`, `new Set(s).add(x)`) | write the deletion by hand (`const n = new Map(m); n.delete(k); return n;`) |
| `vreact synth` on a function whose contract's Lean statement mentions a function that still has a hole (called in the contract, or in the body or `requires` of a function it calls; not in a `@trusted` body or a callee's `ensures`) | not searched ("the contract depends on unfinished function f"): fill or write `f` first |
| `vreact synth` on a `/** @trusted */` function or a component | refused (Lean checks nothing in a trusted body): remove `@trusted` / move the expression into a model function |
| a reducer over a discriminated union calling `@opaque` model functions | supported (contracts are instantiated inside the `switch` arms) |
| invariants about sums (`reduce`) under filter/map | provable, but needs a Lean lemma in `proofs/` (automation handles append, filter, map, `slice`, `toSorted`, `toReversed`, `with` (also swaps `xs.with(i, xs[j]).with(j, xs[i])`), `indexOf`/`findIndex` ranges, `range`, membership, `distinct`, concatenation of string literals, closed facts about literals, decided by evaluation (`String(1 + 2) === "3"`, `" x ".trim() === "x"`, `[1, 2, 3].at(-1) === 3`, also once a test fixes a variable: ``n === 2 ? `n=${n + 1}` : …``), and counts `xs.filter(p).length` under append, delete-by-id, map-updates and mark-all) |
