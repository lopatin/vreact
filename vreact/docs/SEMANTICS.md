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
| `ReadonlyMap<K, V>`, `Map<K, V>`             | `JS.JSMap K V`: entries in insertion order, keys distinct | keys `boolean`/`int`/`string`/enum or an equality-constrained type parameter; values not optional |
| `ReadonlySet<T>`, `Set<T>`                   | `JS.JSSet T`: elements in insertion order, distinct | elements as Map keys |
| `(x: A) => void` (props only)                | callback with a contract                | see §2.4; never data (a function's parameter or result, state, a constant, a local, a hole, an array element or a non-props field: rejected) |
| type parameter `T` of a generic function     | binder `{T : Type}` (+ constraint binders) | abstract; instantiated at each call (below) |

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

Function types and React nodes have no Lean value type: a function parameter or
result, constant, state, local, data prop, callback parameter, `hole<T>()`, type argument
of `new Map<…>`/`new Set<…>` or of a generic call whose type contains one (also inside an
array, option, tuple, Map, Set or a record's fields) is rejected; only a direct
field of a component's props may be a function (a callback, §2.4), and a record
containing one is only a props type (it is not emitted as a Lean type). Types declared by a library (`Date`, `HTMLElement`, React's
other types) are not VTS types, and an interface declared twice (TypeScript merges
the declarations) is rejected.

A record value is a plain object, whose prototype is `Object.prototype`, and a
field is an own property that reads back what was stored. Two kinds of field
names break that and are rejected (in records, union variants and props types,
also as string keys): `__proto__` (an object literal's `__proto__: v` sets the
prototype and creates no property, ECMA-262 B.3.1; an object literal property
`__proto__` is rejected too), and an optional field named like a property of
`Object.prototype` (`constructor`, `toString`, `valueOf`, `hasOwnProperty`,
`isPrototypeOf`, `propertyIsEnumerable`, `toLocaleString`, `__defineGetter__`,
`__defineSetter__`, `__lookupGetter__`, `__lookupSetter__`): when the field is
absent, reading it gives the inherited function, not `undefined` (TypeScript
catches this only for the members its library declares). Required fields with
these names are own properties of every value and are accepted.

`Map`, `Set`, `ReadonlyMap`, `ReadonlySet` (types and constructors), `Array.from` and the other
builtins Map/Set code uses are recognised by their declaration in TypeScript's library, not by
name (as `ReadonlyArray` is: declared in TypeScript's default library and only in library
files): a user type or value of that name, or a declaration in the project that augments one
(`declare global { interface Map<K, V> … }`), is not the builtin. Map keys and Set elements are
the types whose SameValueZero (the comparison JS Maps use) is Lean equality: `boolean`, `int`,
`string` and string-literal enums — not `number` (NaN equals NaN, -0 equals +0), not objects,
arrays or tuples (identity), not optional types (`null` and `undefined` are different keys). A
Map value is never optional: `m.get(k)` is `undefined` for a missing key, which an optional
value would make ambiguous (`JSMap.get` is an `Option V`). In a generic function a key or
element may be a type parameter with an equality constraint (`ReadonlySet<K>` with `K extends
int | string`: Lean `JSSet K` under the function's `[DecidableEq K]` binder), and a value any
type parameter; the body is proved for every Lean type with decidable equality, which includes
the instantiations JS can have (booleans, ints, strings, enums, where SameValueZero is Lean
equality), and each call's instantiation is checked to be one of them (§1.1). A key or element
of an unconstrained or field-constrained type parameter (instantiated with numbers or records:
SameValueZero or identity) is rejected. Maps and Sets are not covariant in VTS: TypeScript
passes a `ReadonlyMap<int, int>` as a `ReadonlyMap<int, number>`, VTS requires the same types
(the Lean types differ).

Rejected: `any`, `as` casts, classes, `this` (also `this` parameters), mutation of
objects/arrays (of Maps and Sets: see §1.2), `==` (except `== null`), `===` on objects,
Maps and Sets (reference identity), generic types, components and arrows (generic
top-level functions are supported, below), exceptions (`try`), `var`, `while`,
recursion (for now), recursive types,
`async`.

**Generic functions.** A top-level function may have type parameters; each is a
Lean binder `{T : Type}` of the definition, abstract in its body, and its constraint
adds what the body may do with values of `T`: an *equality constraint* (`K extends
int | string | boolean | <string-literal enum>`) adds `[DecidableEq K]`, so `===`,
`includes`, `indexOf`, `distinct` and Map keys / Set elements of type `K` (`JSMap K V`,
`JSSet K`) are Lean equality — exactly JS's `===` and SameValueZero on the types `K` may be
instantiated with; a *field constraint* (`T
extends { readonly id: int; … }`) adds one explicit accessor parameter per field,
`(T_id : T → Int)`, and `x.id` on `x : T` is `T_id x` (not a type class: after a
transparent function is unfolded at a call, the accessor `fun x => x.id` reduces to
the record field, which the automation reasons about). The binders come first, in the
order type binders, instance binders, accessors, then the value parameters and
`h_pre`; every contract theorem `f.post…` has the same binders, so it is a theorem for
every instantiation, and `vreact_contracts` applies it to the arguments of each call.
A call passes the type arguments by name, `(f (T := X) (fun x => x.id) xs …)`: they are
inferred by the translator from the VTS types of the arguments (TypeScript's
inference cannot tell `int` from `number`), then from the type the context expects of
the result, then for the arguments typed by their parameter (`[]`, `null`, literals);
`int` and `number` join to `number`, an enum and `string` to `string`; otherwise the
call must write them (`f<int>(…)`). Each instantiation is checked: it is closed and
never nullable — `T | null` with `T = X | null` would be `Option (Option X)` in Lean,
where JS has a single nullish value; so type-parameter parts of a TypeScript type
are non-nullish for the null/undefined analysis, and `x === null` on `x : T` is
statically false —, it is never `number` (no usable equality: `NaN`, `-0`) for an
equality constraint, and for a field constraint it has each field (a record field,
a union's field in every variant or its discriminant, another type parameter's
constrained field) at exactly the constraint's type and nullish kinds. Where a
parameter type has optional parts (`x: T | null`), the argument's must be the
nullish value the declaration names: TypeScript accepts an `int | undefined`
argument there (with `T = number | undefined`), whose `undefined` the body's
`x === null` would not see. Operations that look into a value of `T` (arithmetic,
ordering, `Math.*`, string conversion, string properties and methods, truthiness,
object literals) are rejected also under `T extends int` or `T extends boolean`:
Lean checks the body once for every `T`, and the translator does not take
TypeScript's word that a value of `T` is a number (or a boolean) — every argument
of a `Math` function must have a numeric VTS type. A `@trusted` generic function is
rejected: its axioms would quantify over every Lean type (`decode<T>(s): T` would
inhabit `Empty`; a contract true for the booleans `K extends boolean` admits, like
"two of three are equal", is false at `K := Int`; an accessor parameter need not
be a field read), which is stronger than its JS meaning, where it only runs at
instantiations TypeScript allows. `assume(…)` in a generic body is rejected for the
same reason: Lean keeps the assumed fact as a theorem about the function's
parameters (§1.3), here for every Lean type (`assume(a === b || b === c || a === c)`
under `K extends boolean` would be a theorem at `K := Int`, from which a user proof
derives `False`); `requires(…)` states such a fact for each caller to establish at its
own types. Verified generic functions are sound for the
same reason the other way round: proving the body and contracts for every Lean
type is stronger than needed.

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
  elements (`boolean`, `int`, `string`, enums, equality-constrained type
  parameters, options of these); on objects (identity) and `number` (NaN) they
  are rejected — except a search for the nullish value on optional elements
  (`xs.includes(null)`, `xs.indexOf(undefined)`: `Option.isNone` of each element, for
  every element type, since a present value is never `null`). A callback takes the
  element only (`reduce`'s the accumulator and the element), `map`'s also the index
  (`zipIdx`); an index parameter of the others is rejected with the `forall` form to use.
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
* `x!` carries the obligation `x ≠ null`; `??` maps to `Option.getD`. An optional chain
  short-circuits as in JS: when the base before a `?.` is null/undefined, the whole rest of the
  chain is skipped and the chain is `undefined` (`a?.b.c`, `m.get(k)?.has(x)`,
  `g.get(r)?.get(c)`, `xs?.[i]`); it is a `match` on the base, `some v => some (rest v)` /
  `none => none` (a rest that is itself optional is not wrapped again; the match hypothesis is
  in scope for the rest's obligations). Optional calls `f?.(…)` are rejected; in `a?.b!` the
  `!` asserts the chain's value (TypeScript's reading).
* Maps and Sets (`lean/VReact/JSMap.lean`) are values: `JS.JSMap K V` is the list of entries in
  insertion order with distinct keys, `JS.JSSet T` the list of elements; Lean `=` on them is
  equality of these lists, i.e. observational equality (JS `===`, identity, is rejected). The
  operations follow ECMA-262: `m.set(k, v)` replaces the value of a present key in place and
  appends a new key; `delete` removes the entry (a later `set` appends it again);
  `new Map(entries)` is `set` of each pair in turn (a repeated key keeps its first position and
  its last value), `new Set(xs)` keeps first occurrences, `new Map(m)` is a copy (the same
  value); `get` is an `Option`, `size` the number of entries; `keys()`, `values()`, `entries()`,
  spread, `Array.from` and `for…of` list them in order (also of `o ?? fallback` with an optional
  Map/Set `o`, `new Set(m.get(k) ?? [])`: the entries of `o` when it is present, else those of
  the fallback). An iterator is translated only where it
  is consumed at once (spread, `Array.from(it)`, `for…of`, the argument of `new Map/Set`): JS
  iterators are one-shot and live (they see later mutations), a list is neither. JS Maps are
  mutable objects shared by reference, so a mutation is exact on the value model only when
  nothing else can observe the object. VTS allows `.set`/`.add` in an expression only in a chain
  on a fresh `new Map(…)`/`new Set(…)` (a pure update), and `set`/`add`/`delete`/`clear` as
  statements on a local `const` initialised in the same function with a fresh `new Map/Set(…)`,
  where they rebind the local (as an assignment rebinds a `let`; a `for…of` threads it through
  its fold). A static check of each body (`checkCollectionMutation`) guarantees that no other
  reference to that object exists while a mutation can still run: no mutation of parameters,
  props, state, constants, `let`s or values read from elsewhere; no mutation inside an
  expression; no mutation from a nested function (a callback's mutation would be lost, and it
  may run later); a use of the local other than a read (`size`, `get`, `has`, an iteration
  consumed at once, a copy) — storing, passing, rendering, returning it from a callback (a
  `return` of an array callback or a `useMemo` callback hands it back to the function) — must
  not be followed by a mutation (later in the code or in a later iteration of an enclosing
  loop; a `return` statement of the declaring function itself ends it); a function that runs
  later may not refer to the local when a mutation can follow its creation; and a `for…of`
  over the local may not mutate it (JS would visit the added entries). The check recognises a
  mutation in the form `x.set(…)` (`add`, `delete`, `clear`); every other way to reach a
  mutating method of the library's Map/Set — an index (`m["clear"]()`; Maps and Sets are never
  indexed), the prototype (`Map.prototype.set.call(m, …)`, `Reflect.apply(Set.prototype.add,
  …)`), a method value (`m.set.bind(m)`, `(m.set)(k, v)`) — is rejected wherever it is written.
  The arguments of external writes (`console.*(…)`, `localStorage.setItem(…)`, the value of
  `document.title = …`), whose values are not modelled, are translated with their obligations
  (casts, `eval`, `arguments` and the like are rejected there as anywhere); an effect
  cleanup's arguments and conditions and a timer's delay are translated too, and must in
  addition be data (§2.6: casts, `arguments` and `any`-typed expressions rejected, so their
  static types show every Map/Set they can reach). Such an argument is not an alias: the write prints or
  converts the local where it stands (`console.log("start", n)`, `JSON.stringify(n)` in one), and
  the model reads nothing of it. `console`, `localStorage`, `document` (and the timer functions)
  are recognised by the declaration they resolve to — the library's global —, never by their
  spelling: a fresh local named `console` is mutated by `console.add(1)` like any other.
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
* Builtins are recognised by the declaration a name resolves to, never by its
  spelling: `undefined` is the checker's `undefined` symbol; `Math`, `String`,
  `console`, `localStorage`, `document`, `setTimeout`/`setInterval`/
  `clearTimeout`/`clearInterval` are globals declared only by library files
  (TypeScript's standard library or installed packages); React's hooks and node
  types (`ReactNode`, `ReactElement`, `JSX.Element`) are declarations of React's
  type files, also through an import alias or namespace (`import { useState as
  useS }`, `R.useState`); the `vreact/spec` functions and `int` are declarations
  of the file `import … from "vreact/spec"` resolves to (an installed library),
  also under an alias (`import { type int as I }` is `Int`); `ReadonlyArray`/`Array`
  are the standard library's. A local, parameter, import or project declaration
  spelled like one of them is that binding (`const undefined = 3` is 3; a project
  `type int = number` is `number`; `import * as Math from "./m"` is not
  JavaScript's Math, and a use of it is rejected). A hook is React's only when
  its name, or the namespace before the dot, is bound by an import: React's
  types also declare a UMD global `React`, which a module bundle does not define
  (tsconfig `allowUmdGlobalAccess`, which lets a module use it, is rejected).
  Every scan of what code reads (closures, initialisation order, the order of
  the Lean declarations, dependency cones in the report) resolves the name of a
  shorthand property `{ x }` to the variable `x` it reads, and skips type
  annotations (erased).
* Local helper functions are inlined with each parameter bound to its argument,
  so default values, rest parameters, optional (`x?`) and `this` parameters —
  each would give the parameter another value — are rejected, and so are
  parameter and result annotations with a function type or a React node (no
  Lean value type: the argument and the result are data).
* Module initialisation: a module's top-level code runs in source order when it
  is loaded (after the modules it imports, and re-exports `export … from` are
  imports: no cycles), and a `const` read before its declaration has run throws a
  ReferenceError. The Lean definitions are ordered by dependency, so VTS rejects
  every constant initialiser, `export default x` and module-level `assert(…)` that
  may read — directly or through the functions it calls, transitively — a
  constant of the module declared at or below it (TypeScript checks only direct
  reads; a shorthand property `{ B }` reads `B`); the lambdas of
  `ensures`/`callbackRequires`, which the running code never calls, do not
  count. `export default` of an expression (code run at load) is rejected;
  `export default x` of a name is a binding. A module-level `assert(…)` (a fact
  about an `@opaque` constant of the same module; one about an imported constant
  is rejected) is a theorem placed after every declaration it mentions (its
  constant, other constants, the functions it calls — function declarations are
  hoisted, so they may be declared below the constant).
* Per-file compilation: the bundler compiles each file on its own (Vite: esbuild),
  so it cannot tell that an imported name is a type, and keeps `export { Item }`
  or `export default Item` of an imported type (and the import): the module then
  fails to link. TypeScript reports every construct a per-file compiler cannot
  compile under `isolatedModules` (TS1205, TS1292, …), and VTS always checks with
  it, whatever the tsconfig says (TypeScript's TS1208 for a file that is not a
  module is replaced by VTS's own rejection).
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
  ↦ an obligation that the point is unreachable. Statements after a `return` in
  the same block never run and are rejected (in function bodies, component
  bodies, handlers, effects and timer callbacks alike), so the translation never
  gives them a meaning. Async functions and generators are rejected anywhere in
  verified code: an async function returns a promise (always truthy, e.g. as a
  `filter` predicate) and runs what follows an `await` later; calling a
  generator does not run its body.
* Expressions JS evaluates for their effect only — the arguments of `console.*`
  and `localStorage.setItem`, the value of `document.title = …`, a timer's delay,
  the conditions and arguments of an effect cleanup — are translated as unused
  `let`s at the point where JS evaluates them, so their obligations (index,
  non-null, divisor, preconditions of called functions) are checked; their values
  have no modelled effect. Such an argument may be `JSON.stringify(v)` (also with
  `null, indent`): on a VTS value (a tree of records, arrays and primitives, no
  methods) it cannot throw, so evaluating it is evaluating `v`.
* JSX tags: an identifier starting with a lower-case letter is the HTML element of
  that name (also when a variable of that name is in scope: the JSX transform
  never reads it), a capitalised one the verified component it resolves to.
  Member-expression tags (`<props.as>`: a dynamic element type), namespaced tags
  and custom elements (`<my-el>`, whose behaviour is defined by script outside the
  program) are rejected, and so is `<script>` (inside `<svg>` React inserts a
  script that runs). An HTML element's tag must be ASCII lower-case: the document
  lower-cases names, so `<bUTTON>` would be a `<button>` the layout checks (which
  compare names) would not see. Elements have the namespace react-dom 18.3.1 gives
  them (`getIntrinsicNamespace`/`getChildNamespace`): below `<svg>` (`<math>`)
  every element is an SVG (MathML) element, except below a `<foreignObject>`,
  whose children are HTML. Such an element named like an HTML control (`input`,
  `button`, `select`, `textarea`, `option`, `label`, `form`, `details`, …) has
  none of its behaviour — no value or type, no activation, no form — and react-dom
  still applies its input/select/textarea wrappers by name (a `<select value>`
  there throws on mount): these are rejected; other foreign elements are plain
  content for the event-layout checks of §5 (an SVG `<a href>` is not interactive
  content), have no `value`/`checked`, and a user component inside `<svg>` is
  rejected (it is checked as an HTML tree). Keywords of enumerated attributes
  (`type`) are compared after ASCII lower-casing, as HTML does — not
  `toLowerCase()`, which maps U+212A KELVIN SIGN to `k` (`type="chec&#8490;box"`
  is an invalid type: a text input).
* Elements and attributes react-dom or the DOM reject while rendering are
  rejected: children of a void element (`voidElementTags`: `<input>`, `<br>`,
  `<hr>`, `<img>`, …; even `{false}`, since React tests `children != null`),
  children of a `<textarea>` (with a `defaultValue` React throws; otherwise they are
  its initial value, not elements), a `children` attribute (it is the element's
  children), and `value`/`defaultValue` other than `""` on an `<input>` whose type
  may be `"file"` (its static type, both branches of a conditional, or an enum's
  members; any other expression may be) — setting a file input's value throws.
  Also rejected: `contentEditable` (and `suppressContentEditableWarning`): the user
  could delete nodes React rendered, and React's next commit would throw; `is=…`
  (a customized built-in element, defined by script outside the program); a
  literal `javascript:` URL in `href`, `src`, `action`, `formAction`, `data`,
  `xlinkHref`; `srcDoc` (a document with this page's origin, whose scripts reach
  `parent.document`). Other attributes are data of the element (`VNode.elem`).
* The parameters of a translated function (component, callback, DOM handler,
  array callback, functional update, local helper, top-level function) are bound
  to the arguments by position: a `this` parameter (TypeScript's annotation of the
  receiver, after which the arguments start), a rest parameter (the array of the
  remaining arguments: a DOM handler `(...e) => e.key` reads the key of
  `[event]`, undefined), a default value and an optional parameter are rejected.
* JSX means TypeScript's `react-jsx` transform with React's runtime: the tsconfig
  must have `"jsx": "react-jsx"` (or `"react-jsxdev"`), no `jsxImportSource` other
  than `"react"`, no `jsxFactory`/`jsxFragmentFactory`/`reactNamespace`, and
  `react/jsx-runtime` must resolve into `node_modules/react` or
  `node_modules/@types/react`, and to the same file without tsconfig
  `"paths"`/`"baseUrl"`/`"rootDirs"` (which could redirect it); verified files may
  not contain a JSX pragma (`@jsx`,
  `@jsxFrag`, `@jsxImportSource`, `@jsxRuntime`: TypeScript reads them at the top
  of a file, Babel and esbuild in any comment) nor `@ts-ignore`,
  `@ts-expect-error`, `@ts-nocheck` (VTS relies on TypeScript's errors: element
  and attribute names, null safety, argument types). Both are matched anywhere in
  the text, in any letter case and with any suffix, conservatively.
* JSX text and attribute strings have the value TypeScript's
  JSX transform gives them: text lines are trimmed at line breaks and joined with
  a space (`fixupWhitespaceAndDecodeEntities`), and the character references
  `&#DDD;`, `&#xHHH;` and the HTML 4 entities `&name;` are decoded, also for the
  event-layout checks of §5 (`type="&#115;ubmit"` is a submit button, which the
  TypeScript AST spells raw). References that JSX compilers decode differently
  (names outside HTML 4, `&#X41;`, `&#+65;`, code points above U+10FFFF) are
  rejected, and so are JSX text that Babel's transform gives another value (tabs,
  other whitespace than spaces at line breaks) and attribute strings with a line
  break, written as one or as a character reference (`&#10;`: Babel replaces a
  decoded line break and the whitespace after it with a space).
* `key`, `ref`, `__self` and `__source` are not props in React 18: `createElement`
  and `react/jsx-runtime` take them out of every element's props
  (`RESERVED_PROPS`), so a component never receives them and an HTML element
  never gets them as attributes. A props type with a property of one of these
  names (by the checker's property name, however the type spells it: `"key"`,
  `["key"]`, `k\u0065y`) is rejected, and so are `ref={…}`, `__self={…}` and
  `__source={…}`. (Record fields are named by their property names in general:
  `"b": int` and `["c"]: int` are the fields `b` and `c`.)
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
  run in place and read the current values. A local arrow function (a helper or
  handler, not `useCallback`) is translated where it is called or attached as a
  handler, in the environment of its creation extended with the `const`s and
  `let`s declared after it that are initialised at that point: JS reads them when
  the function runs, which is then or later (a handler runs after the render),
  and each has a single value from its initialisation on (a `let` declared after
  a function that reads it cannot be assigned at all, by the first check);
  variables are identified by their TypeScript symbols, so a name resolves as in
  JS. A use before the declaration (a call in the render, a JSX const) is rejected
  (the call would read it in its temporal dead zone). A `useEffect`, `useCallback`
  or `useMemo` function that reads a local declared after the hook call is
  rejected: its dependency array cannot list it (temporal dead zone), so React
  could keep the function of an earlier render (the `useMemo` factory runs at the
  call: a ReferenceError).
* A DOM handler's event parameter is `DomEvent` (`e.target.value`,
  `e.currentTarget.value`, `e.target.checked`, `e.key`: arbitrary values, fixed for
  the run of the handler). This describes JS only while the handler's own
  statements run: React sets `e.currentTarget` to null after the dispatch, and
  `e.target.value` reads the element's current value. So the event may be read only
  in the handler's statements and in callbacks that run in place there; inside any
  other function created in the handler — a functional update, which React calls
  when it processes the update and again when it rebases it, or a local helper —
  reading it (also `e.preventDefault()`) is rejected: copy the field into a `const`
  first. A field is accepted only where JS reads a string there (`boolean` for
  `checked`), which depends on the element and the handler prop the handler is
  attached to — not on the parameter's type: React's handler types are bivariant
  (`bivarianceHack`), so TypeScript accepts `(e: MouseEvent<HTMLInputElement>) => …`
  as a `<div>`'s `onClick` and types `e.currentTarget.value` as a string, which is
  undefined there (also for a handler passed by name). `e.currentTarget` is the
  element the handler is on (react-dom's `executeDispatch`): its `value` is a
  string on `<input>`, `<select>`, `<textarea>`, `<button>`, `<option>`,
  `<output>` and `<data>` (undefined on most elements, a number on `<li>`,
  `<meter>`, `<progress>`), its `checked` a boolean on `<input>` only.
  `e.target` is the element where the native event happened (`getEventTarget`; a
  text node's parent), any element inside the one the handler is on, so it is
  read only where nothing inside the element can be a target: an `<input>` (void),
  a `<textarea>` (text only), a `<select>`'s `onChange`/`onInput` (`change` and
  `input` fire at the select). There `e.target` and `e.currentTarget` are the same
  element, so the model's one `value` describes both. `e.key` is read only in
  `onKeyDown`/`onKeyUp`/`onKeyPress` (a `SyntheticKeyboardEvent`, whose `key` is
  always a string: `getEventKey`). TypeScript's type of the field must say
  `string`/`boolean` too (it rules out a parameter annotated `any`).

### 1.3 Contracts (`vreact/spec`)

| construct                         | meaning |
|-----------------------------------|---------|
| `requires(c)` in a function       | hypothesis parameter `(h_pre : c)`; every call site must prove it (several `requires` are conjoined in order into one `h_pre`) |
| `ensures((r: T) => c)`            | theorem `f.post : ∀ args, h_pre → c[r := f args]` (a generic function's: also `∀ T` and its constraint binders) |
| `requires(c)` in a component      | the props precondition `pre`; every `<C …/>` must prove it (several are conjoined in order, as in functions) |
| `invariant(c)` in a component     | the state invariant `inv` (after the hooks; several are conjoined in order) |
| `callbackRequires(cb, (…) => c)`  | the contract of the callback prop `cb` holds (§2.4) |
| `assert(c)` / `assume(c)`         | obligation + fact / trusted fact (reported): `c` whenever control reaches it, for every input the declaration's contracts allow; not in a generic function, a `for…of` body, an array-method callback or a functional update |
| `forall exists distinct implies`  | bounded quantifiers, key uniqueness (`List.Nodup`), implication |
| `/** @opaque */` on a function    | callers see only its `ensures` (modular verification) |
| `/** @trusted */`                 | body not verified; contract assumed (reported, appears as a Lean axiom); not on a generic function |
| `hole<T>()`                       | a placeholder for `vreact synth`: `sorry`; while a function has one, its `ensures` theorems are `sorry` too (reported INCOMPLETE) |

A caller uses a contract through its instances: for each call `f a₁ … aₙ` in a goal or a
hypothesis, the automation adds `f.post a₁ … aₙ` — the proved theorem at the call's actual
arguments (`vreact_contracts`). A call under a binder has no actual arguments yet, so the
binders that make it closed are opened first, by ordinary proof steps (`vreact_open`): the
`∀ s` of a robust or rebase-safe outcome (a timer callback, a continuous handler, a functional
update, a dispatch to a transparent reducer whose arm calls `f`), the `∃ a` that
`y ∈ xs.map((x) => f(x))` normalises to, the element of a goal `xs.every((x) => … f(x) …)`.
A call that stays under a binder — inside a quantified hypothesis, which `grind` instantiates
itself — gets no instance there.

A contract is a proposition with JS's evaluation order: the right operand of
`a && b` is translated under the hypothesis `a` (`∃ (h : a), b` when `b` has
proof obligations, plain `a ∧ b` otherwise), `a || b` as `a ∨ ∃ (h : ¬a), b`,
`c ? x : y` as `(∀ (h : c), x) ∧ (∀ (h : ¬c), y)`,
`forall(lo, hi, i => p)` as `∀ i, ∀ (h₁ : lo ≤ i), ∀ (h₂ : i < hi), p`
and `xs.every(x => p)` as `∀ x, ∀ (h : x ∈ xs), p`, so an index obligation in `b`,
`p`, … sees its guard (JS calls a quantifier body only for `lo ≤ i < hi`, or for
the array's elements; `distinct`'s key function runs on every element, and its
obligations are proved for every value of its parameter).

`implies(a, b)` is a function call (vreact/spec: `return !a || b`), so JS evaluates
`b` whatever `a` is. `requires(c)`, `invariant(c)`, `assert(c)`, `assume(c)` and a
module-level `assert(c)` are calls too: JS evaluates `c` at every call, render,
`dispatch` or module load, also with contract checking off — and with it every
quantifier body and callback run inside `c`. In those contracts `implies(a, b)` is
`a → b` with `b` translated where `a` is evaluated: the obligations of `b` (an index,
a `!`, a divisor, a callee's `requires`) must hold without `a`, and `a` narrows
nothing in `b`. Guard them with `!a || b` (`xs.length === 0 || xs[0] > 0`,
`x === null || x.v > 0`) or `a ? b : true`. Only a contract that JS never calls — an
`ensures` lambda, and the expression body of a `callbackRequires` lambda (vreact/spec's
`callbackRequires` ignores it) — reads `implies(a, b)` as `∀ (h : a), b`, so that `b`
may index (and narrow) under `a`. A block body `{ …; return c; }` of a
`callbackRequires` lambda is read as code, its obligations holding for every argument.
(In code, likewise, `implies` evaluates both arguments.)

Several `requires` (or `invariant`) statements are one condition
`c₁ && c₂ && …`: a later one may rely on the earlier ones as guards. (JS evaluates
each of them in turn, but every call site, `dispatch` and `<C …/>` proves all of
them, and every state a component renders satisfies its invariant, so the earlier
ones hold whenever a later one is evaluated.)
Narrowing tests in a guard narrow what JS evaluates under it, as in code — also
in a compound guard: in `b || s.kind === "a" || s.to.length > 0` (left-associated,
any length), `x !== null && y !== null && x + y > 0`, `!(x === null || y === null) || …`,
`implies(x !== null && …, …)` (in an `ensures` or a `callbackRequires` lambda) and `c ? … : …` the later operand is
translated where every earlier operand failed (held), each test becoming a `match`. Such a compound
guard is decomposed only when a later operand needs its narrowing; otherwise it
stays one condition (the normal forms above).

What `assume(c)` trusts is that `c` holds whenever control reaches it, for every
input the enclosing declaration's contracts allow — a function's `requires`, a
component's precondition and invariant (every state the invariant admits, not
only the reachable ones), a callback's `callbackRequires` — not only for the inputs
the program happens to pass. Its proof is `(by vreact_assume)` (VReact/Assumed.lean):
`VReact.assumed` at `∀ hyps, c`, applied to the hypotheses in scope without a value
(`h_pre`, `hpre`/`hinv`, the conditions of the `if`/`match` branches leading to it,
callback-contract and membership hypotheses; proved `have`s follow from them). Lean
keeps that proof as an auxiliary theorem (`f._proof_N`, which a user proof can name),
so its statement must be the fact as stated: `∀ args, h_pre → path → c`. With
`VReact.assumed` at `c` alone it would close over `c`'s variables only — `if (flag)
assume(flag)` would become `∀ flag, flag = true`, from which a user proof derives
`False` without naming the axiom. For the same reason `assume(…)` is rejected where
the translation checks a body for more values than JS gives it: a `for…of` body
(a fold step, for any accumulator and element — as its obligations are), an
array-method callback (a function of any element: the membership `x ∈ xs` is added
only for obligations), a functional update (a function of any state), also through a
helper arrow inlined there — `assume(s >= 0)` on a counter would be `∀ s, s ≥ 0`;
and in a generic function (§1.1), whose theorem would hold for every Lean type. A
handler, effect, timer callback, callback passed to a child or keyed-list item has
the program's context (the snapshot with the invariant, the callback contract, the
item's membership).

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
* `dispatch(a)` ↦ `fun st => {st with r := reducer st.r a h}`. A reducer's
  `requires` may mention only the action, so its proof `h` is made at the dispatch
  site from the snapshot, and it holds for every state `st` React applies the
  action to: React keeps the dispatched action in the queue and passes that same
  value to each reducer call (rebasing, StrictMode replays).

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
  (React's reconciliation requirement; `int` and `string` keys never mix; a string-literal
  enum key is its string, `Key.str (JS.str k)`),
* the children of every element and fragment of which two or more may have an explicit
  `key={…}` store the proof that the keys of the children present are pairwise distinct
  (`VList.withKeys`).  React reconciles the children of one element (or fragment) as one
  array and compares their keys as strings, `'' + key`: `key={1}` and `key="1"` are one key,
  `key={undefined}` is none, `key={null}` is `"null"`.  With two equal keys react-dom's
  `reconcileChildrenArray` keeps one old fiber per key, and the other is neither reused nor
  deleted: its DOM stays, with stale handlers, and it is never unmounted — which the model's
  reconciliation by position cannot describe.  A child contributes the keys of what it can
  render at the top level of the array: an element, the branches of `c ? a : b` and `c && a`
  (under their conditions), the element of a JSX const (its key as evaluated at the
  declaration); a fragment and a keyed list are one child each, with an array — and keys — of
  their own, so a list item's key never meets the key of a sibling of the list.  Two children
  that are always present with the same key written as a string (`key="a"`, also a JSX const
  rendered twice) are rejected; keys written as strings that no two children share need no
  proof; every other case is a `unique-keys` obligation over the keys as strings (string,
  `int`, number, boolean and string-enum keys and their optional forms; another key type next
  to other keyed children is rejected).  The automation proves keys that differ in a literal
  prefix (`` `viewer-${id}` `` / `` `notes-${id}` ``), an `int` key next to a string key that
  is no integer's rendering (`key={id}` / `key="title"`), and different `int` keys,
* every expression JavaScript evaluates during render is kept in the term with
  its obligations, including `key={…}` outside lists (`VNode.withKey`; a key
  change remounts, which is covered because both keeping the state and
  re-initialising it are verified — with distinct sibling keys, React moves a keyed
  child's state only to a child of the same component, which keeping the state with
  new props covers) and boolean children (`VNode.ofBool`, rendered as nothing),
* every parent callback handed to a child stores the proof that, assuming the
  child's callback contract, the parent's invariant is preserved.

A render function that type-checks in Lean can only ever offer the user
invariant-preserving interactions.

### 2.4 Composition: callbacks as assume/guarantee

A child declares `callbackRequires(props.onPick, (i) => 0 <= i && i < props.n)`.
The first argument is the callback prop, taken by the binding it holds, as a call
of it is, never by its spelling: `props.onPick` on the props parameter, or a name
destructured from it — with `{ onPick: pick }` the contract
`callbackRequires(pick, …)` is onPick's, and with `{ onA: onB, onB: onA }`
`callbackRequires(onA, …)` is props.onB's. Anything else (a module function or
another object's property spelled like a callback prop, `Math.max` with a prop
`max`) is rejected. The lambda's parameters are the callback's arguments; its
body is a contract that JS never calls (§1.3: `implies(a, b)` an implication
whose consequent may rely on its guard, as in an `ensures`; guards in scope).

* **Guarantee (child):** every call `props.onPick(e)` (or `pick(e)`, and every
  forward of the callback to a child) must prove the contract.
* **Assume (parent):** the parent's function passed as `onPick` is verified
  under the contract. In Lean the callback returns an `Emit` — the parent
  outcome packaged with the proof that it preserves the parent's invariant
  against the parent's (current) snapshot.

A handler may invoke at most one parent callback per execution path (two would
compose two parent outcomes that were only checked separately). Several
`callbackRequires` for one callback are conjoined, also when one names a parameter
another ignores (`(a) => a > 0` and `(x, y) => y > 0`).

### 2.5 Lifecycle obligations

* `init_inv` — mounting (`useState(init)`, `useReducer(r, init)`) establishes the invariant.
  An initial value may read the props, the state declared before it and top-level
  declarations. React evaluates `useState(x)` in every render but uses `x` only at
  mount, when every earlier state value is its own initial value: so `init` binds
  an earlier state value to its initial value. A non-lazy initial value that reads
  earlier state is also translated in the render, against that render's state (its
  value unused, its obligations checked): JS evaluates it there too (`useState(10 %
  a)` after `a` became 0). A lazy `useState(() => …)` runs at mount only.
* `stable` — when the parent re-renders with new props, React keeps the state:
  `inv props s → pre props' → inv props' s`. An invariant like
  `count <= props.max` is rejected (`PropsStability.tsx`): the parent may lower `max`.

### 2.6 Effects

`useEffect(body, deps)` runs after commit when its dependency values changed.
Its synchronous updates and the timers it registers must be robust and may not
call parent callbacks; `deps` must be exhaustive (otherwise stale closures;
the check sees every reference, including shorthand properties `{ x }`; the same
check applies to `useMemo` / `useCallback`, which the model recomputes, and
re-creates, at every render: exact only because the listed values change, by
React's `Object.is`, whenever a value the body reads does).

Dependencies are *data paths*: an identifier followed by fields declared by the
program (of records, of the props, `?.` or `.`: an optional link reads the same
property), and `length` (arrays, strings) or `size` (Maps, Sets). Each reactive
value the body reads counts as the longest data path it is read through — `m`
for `m.has(k)`, `xs` for `xs.slice(1)`, `props.item?.count`, `xs.length` — and
must be listed, or a prefix of it (`[props.item]` covers `props.item?.count`;
before, nothing covered a props path read with `?.`: `FaDepsOptionalChain.tsx`).
A library method is never a dependency: `m.has` is `Map.prototype.has`, the same
function for every Map (`xs.slice`, `s.trim` likewise), so React never sees it
change, and before, `[m.has]` covered `m.has(2)`: a `useMemo` kept its first
value in React while the model recomputed it, and a broken invariant was
VERIFIED (`FaDepsMemoMethod.tsx`, `FaDepsCallbackMethod.tsx`,
`FaDepsArraySlice.tsx`). Such a dependency is rejected, naming the receiver to
list instead.

An effect's dependency values (`VReact.DepVal`, compared with the previous
render's) follow React's identities: a number, string, boolean or enum by value;
another data value (array, record, Map, optional) as `obj`, "possibly changed"
(the effect runs at least as often as in React, which changes nothing verified:
it is robust, and so is every timer it registers, whichever render registered
it); a setter or `dispatch` contributes nothing (React keeps one function per
hook); a local helper arrow is `obj` (a new function at every render: the
effect runs after every render, as in React); a `useCallback` function
contributes the dependency values of its own dependencies (React returns the
cached function until one of them changes, so it changes exactly when they do:
`useCallback(f, [])` listed in an effect runs it once, as `[]` does;
`FaDepsEffectUseCallback.tsx`, `FaDepsEffectHelper.tsx`). A parent callback
(`props.onPick`, or destructured) is rejected as an effect dependency, also
through a `useCallback` that lists one: an effect never calls one, and when the
parent passes a new function is not modelled. The props object itself is not an
effect dependency either (a `useMemo` / `useCallback` may list it: the same props
object has the same fields): list the fields the effect reads.

The model has no cleanup step, so a returned cleanup is restricted statically:
it must be an inline function that only calls `clearTimeout` / `clearInterval` and makes external writes
(`console.*`, `localStorage.*`, `document.title = …`) with pure arguments,
possibly under `if`/`else` with pure conditions —
no setters, `dispatch`, parent callbacks or local helpers. JS still evaluates
its conditions and arguments when it runs, with the values it captured: those
at the effect's `return` (a captured `let` is never reassigned after the cleanup
is created, §1.2, and nothing in the effect follows its `return`). So the cleanup
is translated there, as an unused `Unit` term inside the effect's setup outcome:
its obligations are checked under the facts that hold at that `return` (the
effect's early returns and branches). A condition on a timer handle (`id !==
null`, `id`) is decided statically: browsers return a positive integer. The
cleanup may be returned at the end of the effect body or of a branch of it;
statements after a `return` are rejected (JS never runs them). A timer handle
is the `const` a registration `const id = setTimeout(…)` declares; it is bound
(as a handle, not a VTS value: it can only be cleared) once that statement has
run, so a cleanup can clear it, or test it, only when it is returned after the
registration on its path. A cleanup returned earlier — from a branch before
`const id = …` — would read `id` in its temporal dead zone when React calls it
(a ReferenceError; TypeScript does not flag a use inside a closure): rejected.
"Pure" (for the arguments and conditions of a cleanup, and a timer's delay, which
are also translated with their obligations) is checked
syntactically and by TypeScript symbol: calls only of the library's reading methods (by the
lib interface that declares them: array methods other than the mutators, string, number and
boolean methods, `Math`, `JSON.stringify`, the reads of `Map`/`Set`, `Object.prototype`'s),
`String`, spec functions and the module's functions; a function value only as the callee of
a call — not passed, stored in an object or array, or chosen by `?:` (inline callbacks, which
are checked themselves, aside); no `new`, `delete`, `await`, tagged templates, assignments,
`++`/`--`, casts, `arguments` or `any`. So the code cannot mutate a state value in place
(`xs.push(1)`, `m.get(k)!.push(x)`, `Array.prototype.push.call(xs, 1)`) or reach a setter
(`[1].map(setN)`, `String({ toString: setN })`).
Running a robust effect any number of times (StrictMode) is safe.

A timer is registered only by a statement at the top level of the effect body
(`setTimeout(…)` / `const id = setInterval(…)`, with at most a delay argument,
which is evaluated — checked — at that statement). Its callback is translated in
the environment of the effect body at the registration: each top-level `const`
declared before it is translated again inside the task, as the effect body
translates it — JS evaluated it once, before the registration, from the snapshot
and the effect's earlier consts, and it keeps that value. Not bound there, and
rejected if the callback reads them: the body's `let`s, a local Map or Set the body
mutates (re-translating its declaration would give its value before the
mutations), and a `const` whose value has obligations of its own (they are checked
in the effect body, not repeated). The callback is checked under the
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
that environment without obligations of its own (it may read the consts bound
there); others are left out, which only weakens the facts.
(`CxTimerGuard.tsx`: the guarded countdown
`if (left <= 0) return; setTimeout(() => setLeft(left - 1), …)`.)

Hooks (`useState`, `useReducer`, `useEffect`, `useMemo`, `useCallback`) are
matched by React by call order, so they must be top-level statements of the
component, before any statement that may return (an `if`, a `switch`, …); a hook
in a branch, loop, handler or closure is rejected. Parentheses around a hook call
(`(useEffect(…))`, `const [n, setN] = (useState(0))`) do not change it. The other
React hooks (`useLayoutEffect`, whose updates are synchronous during the commit,
`useRef`, `useContext`, …) are not modelled and are rejected, as is a hook other
than `useEffect` called as a statement with its value unused.

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
functions — also in keys and boolean children), and neither do handlers, effects,
timers and cleanups (also the arguments of external writes and timer delays,
whose values are not used); keys are
distinct (in keyed lists, and among the keyed children of every element and fragment,
compared as strings); child preconditions hold; callback contracts hold in both directions;
hook rules hold (static checks). For every function: its body is safe and its
`ensures` hold.

## 5. The trusted base — what is *not* verified

* **The translation** from TypeScript to Lean (≈3k lines of TypeScript). It is
  structural and syntax-directed; the regression suite pins its behaviour. The
  value model of Maps and Sets relies on its alias analysis (§1.2): that a mutated Map or
  Set is referenced by nothing else while it can still change, and that every mutation is
  written `x.set(…)`/`add`/`delete`/`clear` (other routes to the library's mutating methods are
  rejected syntactically, by their TypeScript symbol; in a cleanup's arguments and conditions
  and a timer's delay, which must be data, the static checks also rely on TypeScript's types,
  with casts, `arguments` and `any` rejected, and on the list of the library's reading methods
  of §2.6). Globals (`console`, `localStorage`, `document`, the timer functions) are
  recognised by their declarations in the library files. Its
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
  …), and within a module a function or constant named like a type of the
  module (TypeScript keeps the two apart; both would be `VTS.m.Limits`).
  Namespaces may otherwise nest (`src/ui/Board.tsx` next to a component
  `Board` of `src/ui.tsx`). User lemmas `proofs/<path>.lean` are imported by
  that module's `View.lean` and by the `Defs.lean` of every module importing it
  (unless that would close an import cycle); `proofs/Base.lean` by every
  `Defs.lean`. When every importing module can import them, the `ensures`
  theorems of the module's functions that no other function or constant of the
  module uses are proved after the lemmas, in `Posts.lean` (imported by the
  module's `View.lean` and the importing modules' `Defs.lean`).
  Generated files set `autoImplicit false`, so a binder the translation failed to
  emit is a Lean error, never an auto-bound variable.
  For generic functions (§1.1), Lean checks that each call's type arguments and
  accessor arguments are well-typed and proves the body and contracts for every
  instantiation (the type parameters are abstract, so the body cannot depend on
  what they are); what the translator alone ensures is that the parametric model
  means what JS does at each call: the instantiation is inferred from the
  arguments' VTS types (also through Map and Set types) and is never nullable, an
  equality-constrained one is a type JS compares by value (so a Map key or Set
  element of that type parameter is compared by SameValueZero exactly as by Lean
  equality), the accessor passed for a constrained field reads that field
  (`fun x => x.f`, a union's shared-field accessor, or a type parameter's own
  accessor) at exactly the constraint's type and nullish kinds, and an argument for
  a parameter with optional parts has the nullish value its declared type names
  (also inside arrays, tuples and Map values).
  No `@trusted` declaration is generic (§1.1): its axioms are about the closed VTS
  types of its signature, all of them inhabited, so what they assume is its type
  and contracts at those types — what the reviewer of the declaration checks. Nor
  does a generic body `assume(…)` (its fact would be a theorem for every Lean type).
* **The report.** Every obligation runs under `vreact_ob` (`VReact/Budget.lean`),
  with its own heartbeat budget (per obligation also under parallel elaboration:
  Lean's heartbeat counter is per thread, and an obligation runs on one thread; the
  cost of realizing an auxiliary declaration that several obligations share goes to
  the first one that needs it; heartbeats count allocations, and a walk over a goal
  allocates little, so the walks over the whole goal that collect the calls with
  contracts, the counts, the `Nodup` sources and the index terms, and the case sizes
  after a timeout, visit each distinct subterm once: their cost is the size of the
  goal as Lean shares it, not as a tree, which nested `%` or `let`s can make
  exponentially larger; the automation's other walks, on particular hypotheses and
  subterms, and Lean's own tactics such as `grind` are not bounded this way), and
  reports its result at its marker: the
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
  are failures, never proofs. After running out of the budget, the automation
  looks for the case that fails, as a diagnosis: the goal's cases (the branches
  of its `if`s and `switch`es, named as Lean's `split` names them, outermost
  first: `isTrue`/`isFalse` the branches of an `if`, also of a `switch` on a
  number or a string, which is a chain of `if`s, one per body; `h_k` the k-th
  alternative of a `match`, and a `switch` on a union or an enum has one per
  `case` label in the order written, then one for the rest, `default` wherever
  it is written; conditions in the translation, such as the sign test of `%`,
  split too) are tried alone,
  smallest first, with a tenth of the budget each and half of it in all, until
  one fails; the failure text adds how many were proved, did not finish or were
  not tried, and the goal of the case that failed (or of the first that did not
  finish). The obligation stays failed; a declaration's `maxHeartbeats` counts
  each of its obligations twice to leave room for this. `vreact verify` prints a
  failure's text in at most 18 lines (`--full`: all of it). A longer text is
  shortened step by step, each step only while it is still too long: a text with
  several goals (after a timeout: the goal as stated, then the case that failed)
  keeps only the last one, so the hypotheses shown are those of the conclusion
  shown; its multi-line contract instances (`hcontract…`, the facts of the
  callees' `ensures`) become one line that names and counts them; then its
  multi-line let-definitions (`x : T := match …`, code the source shows), from
  the top, likewise; then its other multi-line hypotheses, from the top, each one
  only if that frees no more lines than are still needed, but not the hypothesis
  right above the conclusion (often the negated goal or the last case split) when
  it fits; last, the conclusion is cut to 3 lines and, from the conclusion up,
  each hypothesis is shown whole while it fits (a multi-line one that does not
  fit as one line that names it, where it was), and the hypotheses farthest from
  the conclusion are left out, named and counted by one line `… (k earlier
  hypotheses: …)`. Every line that stands for others
  ends in `--full shows it` (or `them`); every other line is a whole line of
  Lean's text, so the short hypotheses next to the conclusion (usually the
  branch conditions that decide the case) stay in view. Each failed or not-checked obligation is
  listed with its position, its kind (`[precondition]`, `[handler]`, …) and, for
  a failure, a description; an argument in a description is shown whole up to
  40 characters (an action dispatched to a reducer up to 100), a longer object or
  array literal field by field (each value up to 24 characters), so a field such
  as `qty: qty - 1` stays visible; the text of a contract (a postcondition, an
  assertion, a fact) is shown whole up to 120 characters, a longer one by the
  arguments of its outer call or the operands of its outer operator, the short
  ones whole and each longer one by its start and its end; whitespace is
  collapsed except inside string, template and regular-expression literals,
  whose contents are shown as written (a line break as `\n`); a call shown by
  its arguments keeps its type arguments. (A proof that refers to another declaration whose
  proof was admitted — a callee's failed contract — is a proof modulo that
  contract and counts as proved; the item is `INCOMPLETE` by its axioms.) A failure is not a Lean error, so the module and every module
  importing it are still built and checked; the admitted goal shows as
  `sorryAx` in the axioms of whatever depends on it. `vreact verify` counts an
  obligation as proved only if every copy of its marker has `vreact:ok`, none
  has a failure (a `vreact:` warning or an error), its file was elaborated to
  the end (the `vreact:checked` sentinel), its declaration has no other error,
  and its item's axioms are reported, with any `sorryAx` among them coming from
  a reported failure, hole or error (of the item, an item it uses, or a user
  proof); missing evidence means *not checked*, never proved (an obligation
  proved in a file whose item's axioms are printed by a file Lean did not check
  to the end — a postcondition theorem in `Posts.lean`, after a user proof it
  imports failed — gets that file's reason). Every component,
  certificate, function, contract, constant and fact has a `#print axioms`;
  `sorryAx`, a `declaration uses 'sorry'` warning (other than an admitted
  goal's) or an error in one of its declarations makes it `INCOMPLETE`: an item
  whose own obligations are proved is `INCOMPLETE` when it relies on one that is
  not, and the report names that dependency. `UNCHECKED` (no axiom report) is
  left for items Lean never got to: lake or import errors, an error that stopped
  a file. Lake errors without a position (imports, build cycles) are shown and
  make the result not verified. An axiom report, the sentinel or `vreact:ok`
  counts only when Lean printed it at the
  generator's own `#print axioms X` / `#vreact_assumed X` / sentinel line /
  `vreact_ob` token, as a
  message of that generated module's own Lean run (`vreact_ob` drops `vreact:`
  messages that code running inside the obligation logs; several reports for one
  name are joined). The messages are never read from the text lake prints, where
  a line of one message (a user proof printing `✔ [9/9] Built VTS.m.Posts` and
  `info: VTS/m/Posts.lean:…: vreact:ok`) cannot be told from lake's own lines:
  each module's messages are the entries of the build log lake stores with it
  (`.lake/build/lib/lean/<module>.trace`, one entry per message), and a module
  whose build failed (lake keeps no log of it) is elaborated once more with
  `lean --json`. Lake's text is read only for lake's own errors, which can only
  take away (`RlSmuggledForge`).
* **The build directory** (`.vreact/.lake`) holds, for every module, its
  `.olean` and the log lake replays instead of running Lean when the module is up
  to date — files anyone who can write the project can change (a committed
  `.vreact/`, an `"out"` directory elsewhere, a shared cache, an agent editing
  build files). So `vreact` keeps a record of the build directory it left
  (`<library>/.lake/vreact-builds/`, outside the project: the hash of every file
  under `.vreact/.lake` and of `lake-manifest.json`, the modules whose logs are
  current, the modules certified below, each with a key of its inputs — its
  source, the keys of the project modules it imports, the toolchain and the
  library's built modules). A build directory that is not exactly that one is
  removed and everything is built again; before a build, the outputs of every
  module whose key changed are removed, so afterwards a module has a log exactly
  when the log comes from a Lean run on its current inputs (stale logs of a
  module whose rebuild failed are not left behind). Lake's shared artifact cache
  is off for the project and the library (`enableArtifactCache = false`,
  `LAKE_ARTIFACT_CACHE=false`). (`RlCachePoison`: a doctored log made a false
  ensures VERIFIED with no Lean run.)
* **The kernel re-check** (`lean/Certify.lean`, the `vreact-certify` program of
  the library). Lean's elaborator can add a declaration without the kernel
  (`debug.skipKernelTC`), and the axiom report cannot show it. After the build,
  `vreact` loads the built modules in a fresh process and replays every
  declaration of the generated modules and the user proofs into Lean's kernel
  (`Lean.Kernel.Environment.replay`, lean4checker's method); for each user proof
  module it also checks what the module added besides its declarations: entries
  of environment extensions other than those of theorems, definitions (equation
  lemmas, matchers, compiled code, documentation), `@[simp]`/`@[vreact_simp]`/
  `@[grind …]` and `grind_pattern` (also on a library lemma, `attribute [simp]
  VReact.JS.…`: Lean records, for its import linter, that the lemma's users may need
  the module, `Lean.indirectModUseExt`, which changes nothing else; `RlProofsAllowed`)
  (so no syntax, macro, elaborator, instance,
  alias, coercion, simproc, initializer, …), axioms, definitions in the
  namespaces `VTS`/`VReact`, and declarations that use an axiom other than
  Lean's standard ones, `sorryAx` and the generated `@trusted` axioms (in
  particular `VReact.assumed`, which the report reads as the source's `assume(…)`
  facts, and the axioms of native evaluation). A module that fails is an error
  (of the user proofs, or internal for a generated module), and every generated
  module that is not certified — it failed, or it imports a module that failed —
  is broken as a whole: no obligation in it counts as proved and no item with a
  declaration in it is `VERIFIED` (nor any item using one), whatever Lean
  printed while elaborating it (`RlSmuggledSkipKernel`, `RlSmuggledMacro`,
  `RlSmuggledInstance`, `RlSmuggledAssumed`). Modules certified by an earlier
  run with the same key are not replayed again.
  A generated declaration
  with an error makes every obligation of its item unproved; when Lean still
  reports clean axioms for its name, something else (e.g. a declaration of a
  user proof) stands in for it, so every item that uses it, directly or not, is
  `INCOMPLETE` as well. An axiom that is neither Lean's standard ones, nor
  `VReact.assumed`, nor emitted for a `@trusted` declaration (e.g. one declared
  in a user proof, which the kernel re-check below also reports as an error that
  breaks every module importing it) makes the items that depend on it `TRUSTED` (the verdict
  says "modulo axioms from outside the translation"), except an axiom of native
  evaluation — `<decl>._native.<tactic>.ax_…` (`native_decide`, `decide +native`,
  `bv_decide`), `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` —
  which trusts Lean's compiler instead of its kernel: the items that depend on it
  are `INCOMPLETE` and the result is NOT VERIFIED (`RlNativeAxiom`).
  `VReact.assumed` proves anything, so it stands for the program's `assume(…)`
  facts (`ASSUMES`) only where `#vreact_assumed X` (VReact/Assumed.lean), written
  after each `#print axioms X`, finds in `X`'s dependency cone (in the kernel's
  terms) no declaration outside the generated code — a user proof's, under
  whatever spelling: the axiom's name, a renaming `open`, a wrapper definition, a
  tactic — whose own type or value uses the axiom: such a declaration states an
  unproved fact of the proof file, i.e. it is an axiom of its own, and the items
  that rely on it are `TRUSTED`, with the declaration named (`assumedByProofs` in
  `--json`). An item whose axioms include `VReact.assumed` without that report
  (printed at the generator's `#vreact_assumed X` line) is `UNCHECKED`. A user
  proof that uses the theorem Lean keeps of an `assume(…)` (`f._proof_N`, §1.3)
  uses the program's fact as stated: `ASSUMES`. (This audit is a third line of
  defence: the whitelist below rejects the identifier `assumed` and the tactic
  `vreact_assume` in proof files, and the kernel re-check above rejects a proof
  module with a declaration that uses `VReact.assumed` directly, which breaks every
  module importing it — `GxAssumeInProofs`.)
* **User proofs** (`proofs/**/*.lean`, `proofs/Base.lean`) are imported into
  generated files, so whatever they declare takes effect while the translation is
  checked. Before Lean runs, `vreact` checks every proof file against a whitelist
  (`lean/ProofCheck.lean`, the `vreact-proofcheck` program of the library): it
  parses the file with Lean's own parser, in exactly the environment the file is
  elaborated in — `Init` + `VReact` when its imports reach `VReact` or a generated
  module (directly or through the proof files it imports), `Init` alone otherwise
  (generated modules and proof files add no syntax); `open`/`namespace`/`section`/
  `end`/`set_option` are elaborated, so scoped syntax and options are what Lean
  will see (`RejectRlEnvImports`: a file importing only `Init.Core` was parsed with
  `VReact`'s syntax, where `m! "A{"…"}B"` hid a `macro_rules` in what the check read
  as a string) —, rejects a file that does not parse completely, and accepts
  only: plain `import`s of `VTS.…` (generated modules), `Proofs.…` (other proof
  files, which must exist, without a cycle), `VReact` (the whole library, not a
  part such as `VReact.JS`) and `Init` (not a part such as `Init.Core`);
  `theorem`, `def`, `abbrev`, `example` (modifiers: doc
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
  blocks the build) — as a command, with `in`, inside terms and tactics, and in
  any other syntax with the keyword `set_option` (grind's interactive `set_option
  … in`, `RejectRlGrindOption`: there `debug.skipKernelTC` let `decide +kernel`
  prove `False`); and
  in terms and tactics anything but `run_tac`, `by_elab`, `unsafe`, `include_str`,
  `native_decide`, `+native`, a `decide (config := …)` value (`⟨false, true, true,
  false⟩` is `+native`; write `+kernel`, `+revert`, …), the `bv_decide` tactics
  (also in `grind =>`/`sym =>`; they run an external SAT solver), `idbg`,
  `dbg_trace` and the `dbgTrace…` functions (they print to Lean's output), the
  identifier `assumed` (`VReact.assumed` in any spelling: the axiom behind the
  source's `assume(…)` facts, `RejectRlAssumed`) and the tactic `vreact_assume`
  (the translator's proof of an `assume(…)`, which applies that axiom), the
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
  report of every item that uses them. After the build, the kernel re-check
  (above) replays every declaration through the kernel and checks what each
  proof module added, independently of this syntax check. The trusted parts are
  Lean's kernel, the re-check's list of what a proof module may add, and — for
  what runs while Lean elaborates a proof file (code execution, files written,
  output), which no check after the build can undo — Lean's parser and this
  whitelist.
* **The declarations of the libraries.** The program's types come from
  TypeScript's standard library, installed packages (`node_modules`: React's
  types, `vreact/spec`, and anything an installed package declares or augments,
  e.g. a `declare module "react"` adding attributes) and the VTS sources, and the
  translation trusts the library declarations to describe what runs. The
  project cannot change them: VTS sources must be modules (a script's
  declarations are global and its interfaces merge with the libraries'), and
  `declare …`, `declare global`, `declare module`, namespaces and a project file
  in the program that is not a VTS source (a `.d.ts` reached by `/// <reference
  path>`, tsconfig `typeRoots`/`types`/`paths`) are rejected, as is
  `/// <reference no-default-lib="true"/>`. What JSX means is configured as
  well: only `"jsx": "react-jsx"` (React 18's automatic runtime) is accepted — no
  other `jsxImportSource`, no `@jsx…` pragmas (in any comment and any letter
  case: esbuild and Babel read them anywhere in a file, TypeScript in its leading
  comments with the name lower-cased), no `tsconfig.json` inside the source
  directories (the bundler compiles a file with the settings of the tsconfig.json
  nearest to it). A project without a tsconfig.json is checked with vreact's
  defaults, and the bundler is trusted to compile it the same way (Vite reads the
  nearest tsconfig.json above the project, if any).
* **TypeScript's checker.** VTS relies on the program type-checking without
  errors (null and undefined, the types of library and React declarations,
  imports): `@ts-ignore`, `@ts-expect-error` and `@ts-nocheck` are rejected
  anywhere in a verified file, in any letter case and with any suffix
  (TypeScript matches the line directives as prefixes — `@ts-ignored` — and
  lower-cases pragma names — `@TS-NOCHECK`); so is tsconfig `allowUmdGlobalAccess`
  (a library global used without an import, which a module bundle does not
  define). Compiler options are a whitelist: every check of the strict family is
  required (none set to false), `noCheck` (no type checking at all),
  `resolvePackageJsonExports/Imports: false` and any option vreact does not know
  are rejected; an invalid tsconfig is an error (an option name the bundled
  TypeScript does not know is ignored, as TypeScript ignores it). The program is checked with
  `isolatedModules` (see "Per-file compilation").
* **The bundler keeps every statement.** Bundler annotations in comments
  (`@__PURE__`, `#__PURE__`, `@__NO_SIDE_EFFECTS__`, any `@__X__`/`#__X__`) are
  rejected anywhere in a verified file: a production build (esbuild's minifier,
  Rollup's tree-shaking) deletes an annotated call whose result is unused, with
  its effects. The minifier and tree-shaking are trusted to preserve the meaning
  of code without such annotations, and the build configuration (vite.config:
  plugins, `esbuild` options such as `jsxImportSource`, `pure` or `drop`,
  `define`, `resolve.alias`) to be React's default setup, which VTS cannot see.
* **Module resolution.** TypeScript must read the files that run. The bundler is
  trusted to resolve a relative specifier like Vite's default resolution
  (relative to the importing file; without an extension the first of `.mjs`,
  `.js`, `.mts`, `.ts`, `.jsx`, `.tsx`, `.json`, then a directory's
  `index.*`; a `.js` path that does not exist as its `.ts`/`.tsx` source) and
  bare specifiers through `node_modules`, with no aliases (`resolve.alias` in
  the Vite config is outside the subset). VTS checks every import of a verified
  file against that: a verified module is imported by a relative path that
  leads there, by itself, to the file TypeScript read (TypeScript-only settings
  — tsconfig `paths`, `baseUrl`, `rootDirs`, `moduleSuffixes`, package
  `imports` — would make them differ, and so would a `b.js` next to `b.ts` for
  `"./b"`); `react`, `vreact/spec` and the `react/jsx-runtime` of JSX must
  resolve to the installed packages' declarations, and to the same files
  without those settings.
* **The JS runtime model** (`JS.lean`, `JSMap.lean`): e.g. that `Array.prototype.slice` behaves
  like `JS.slice`, and that a JS `Map`/`Set` with keys of the admitted types behaves like
  `JS.JSMap`/`JS.JSSet` (insertion order, SameValueZero as Lean equality on those types). Definitions follow ECMA-262 directly; where ECMA-262 leaves a
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
  external effects with no state change (their arguments are evaluated and
  checked; the writes themselves are assumed not to throw — a full storage quota
  or a `SecurityError` from `localStorage` would abort the handler); reading
  external data is not modelled. A DOM event is an arbitrary `DomEvent`: the model
  assumes nothing about the values the user enters.
* **The JSX transform:** the meaning of JSX is TypeScript's `react-jsx` transform
  (tag names, whitespace of JSX text, character references), cross-checked against
  Babel's: JSX text on which the two disagree (a tab, a whitespace character other
  than a space next to a line break, a reference to whitespace there), attribute
  strings with a line break, raw or as a character reference (Babel replaces a
  decoded line break and the whitespace after it with a space), and references
  that compilers decode differently are rejected. Other compilers (esbuild, SWC)
  are assumed to agree with them on what is accepted. The props React's JSX
  runtime keeps out of an element (`key`, `ref`, `__self`, `__source`) are those
  of react 18.3.1's `RESERVED_PROPS`. The configuration is checked (tsconfig
  `jsx`/`jsxImportSource`/`jsxFactory`/`reactNamespace`, the resolution of
  `react/jsx-runtime`, JSX pragmas in verified files); the bundler is assumed to
  compile JSX as that tsconfig says (esbuild and Vite read it; a Babel
  configuration of its own, e.g. a classic-runtime preset, is not checked).
* **DOM event fields:** which elements have a string `value` (`<input>`,
  `<select>`, `<textarea>`, `<button>`, `<option>`, `<output>`, `<data>`) and a
  boolean `checked` (`<input>`), that nothing inside an `<input>`, a `<textarea>`
  or (for `change`/`input`) a `<select>` is an event target, and that React 18.3.1
  gives `e.currentTarget` the handler's element and `e.key` a string in keyboard
  handlers (HTML standard; react-dom `executeDispatch`, `getEventTarget`,
  `getEventKey`) — not TypeScript's bivariant handler types. These are HTML
  elements: the namespace of each element is react-dom 18.3.1's
  (`getChildNamespace`: SVG below `<svg>`, MathML below `<math>`, HTML again below
  an SVG `<foreignObject>`), and a component's root is assumed to be mounted in an
  HTML container (`createRoot` in `main.tsx`, outside the program).
* **Elements and attributes:** the elements and attributes react-dom 18.3.1
  rejects while rendering are those of `assertValidProps` (`voidElementTags`,
  `dangerouslySetInnerHTML`, `style`) and of its textarea wrapper, and the only
  DOM setter React calls that throws is a file input's `value`. An attribute
  other than those rejected (§1.2) is data with no behaviour the model needs; in
  particular what a link, an `<iframe>`, `<object>` or `<embed>` loads is assumed
  not to run script in this page — a `javascript:` URL built at run time, or a
  same-origin frame, could change the DOM React manages.
* **Outside the subset:** the entry point (`main.tsx`), React itself, the DOM,
  CSS. No other script, browser extension or user edit changes the DOM React
  manages (the user cannot: `contentEditable` is rejected; an extension that
  rewrites text nodes, e.g. a page translator, makes React's updates throw).
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

Lean's kernel checks every proof (once while Lean elaborates, and again in a
fresh process after the build: the kernel re-check above); `sorry`, `@trusted` and `assume(…)`
(`VReact.assumed`, reported `ASSUMES`; only the generated code may use it, at the
source's `assume(…)` sites — a user proof that does is rejected, and an item relying
on one that got through is `TRUSTED`) show up in the axiom report, so nothing
unverified can be mistaken for verified.

`vreact synth` is not part of the trusted base: its random tests only prune
candidates. It reports "proved by Lean" (and `--write` writes a fill) only when
Lean elaborated the function and all its postcondition theorems, none of the
function's obligations failed, and their axioms contain no `sorryAx` — so a
function with several holes is proved once all are filled, a `@trusted`
function is refused, and a failure elsewhere that keeps the function from being
checked is reported as "not proved". The written text is the text Lean checked.
A proof whose axioms include @trusted declarations, `assume(…)` facts or axioms of
user proofs (also user-proof declarations that use `VReact.assumed`) is
reported relative to them (`--json`: `"status": "proved-relative"` and
`relative_to`). A generic function is tested at `int`/`string` instantiations (also
as the keys, values and elements of random Maps and Sets; a
witness record with the constrained fields for a field constraint; an optional
constrained field absent as `undefined`, as TypeScript allows), and generic helpers
are offered at instantiations from the hole's types; the tests only steer the
search, and Lean proves the fill for every instantiation. Synth types candidates with the narrowing the translator has at
the hole (with the variants left after exclusions, which the translator splits
on when a fill needs them), and searches a hole once per fill of the earlier holes a call can
also evaluate (holes in different cases or branches are searched once); both
only steer the search — Lean still checks every fill of a function together. The
random inputs come from a seeded generator, one per hole (its seed made from the
run's seed, `--seed N`, default 1, the function's name and the hole's position), so
a run tests the same inputs whatever order the holes are searched in, and two runs
say the same up to the 60 s time limits; the seed, too, only steers the search.
