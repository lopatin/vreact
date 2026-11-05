# Walkthrough — building a formally verified Kanban board

This walkthrough builds `examples/kanban` from an empty folder to a **fully
verified** React application: 7 components, a reducer, 12 model functions,
79 kernel-checked proof obligations, and a whole-app certificate
(`App.certificate`, an instance of the React-runtime soundness theorem) that
depends on nothing but Lean's three standard axioms.

It goes **top-down for the UI** (the App is verified first against contracts of
children that do not exist yet) and **bottom-up for the logic** (the model is
specified, partly synthesized, and verified before anything renders). Every
output below is a real run, recorded in [`walkthrough/`](walkthrough/) next to this file;
the app is `examples/kanban` in the repository that contains the tool.

The finished app: three columns, a WIP limit on *Doing*, add/move/delete cards,
a filter, a selected-card panel, a notice that dismisses itself on a timer.

---

## Step 0 — Set up

```bash
npm create vite@latest kanban -- --template react-ts   # or any React+TS project
cd kanban && npm i ../../vreact                         # provides `vreact` and `vreact/spec`
```

`tsconfig.json` must have `"strict": true`. Add `vreact.json`:

```json
{ "src": "src", "exclude": ["main.tsx"], "proofs": "proofs", "out": ".vreact" }
```

`main.tsx` (which only mounts `<App/>`) stays outside the verified program.

---

## Step 1 — Specify the model first

`src/model.ts` states **what** the board is and which operations exist, before
any implementation. The invariant is ordinary TypeScript:

```ts
export type ColumnId = "todo" | "doing" | "done";
export type Card = { readonly id: int; readonly title: string; readonly points: int };
export type Board = {
  readonly todo: readonly Card[]; readonly doing: readonly Card[]; readonly done: readonly Card[];
  readonly nextId: int; readonly wipLimit: int;
};

/** The board invariant: unique ids below nextId, valid cards, WIP limit respected. */
export function wellFormed(b: Board): boolean {
  const cards = allCards(b);
  return (
    distinct(cards, (c) => c.id) &&
    cards.every((c) => c.id < b.nextId && validTitle(c.title) && validPoints(c.points)) &&
    b.wipLimit >= 1 &&
    b.doing.length <= b.wipLimit
  );
}
```

Operations get **contracts and no bodies**. Reducers must be *total* (React may
apply them to any queued state), so contracts are implications rather than
preconditions; `@opaque` makes callers reason through the contract only:

```ts
/** @opaque */
export function moveCard(b: Board, id: int, to: ColumnId): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, null));
  return hole<Board>();
}
```

```
$ vreact verify
pending (hole() / sorry): addCard, deleteCard, moveCard, setWipLimit
◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)
```

---

## Step 2 — Synthesize what can be synthesized

`vreact synth` enumerates well-typed implementations smallest-first, runs the
real JavaScript on random inputs against `requires`/`ensures`, and proves the
survivors in Lean:

```
$ vreact synth src/model.ts
hole in addCard: Board   scope: b, b.todo, b.doing, b.done, b.nextId, b.wipLimit, title, points
  candidate passes 400 random tests: b
  ✔ proved by Lean: b
hole in deleteCard: …
  ✔ proved by Lean: b
…
```

**The synthesizer just proved the spec too weak:** `return b` satisfies every
contract — doing nothing preserves well-formedness and keeps all cards. A
verified spec is only as good as what it says, so we add *functional*
requirements:

```ts
// addCard
ensures((r: Board) => implies(validTitle(title) && validPoints(points),
                              r.todo.some((c) => c.title === title && c.points === points)));
// deleteCard
ensures((r: Board) => allCards(r).every((c) => c.id !== id));
// moveCard: if the card exists and the target has room, it ends up in `to`
ensures((r: Board) => implies(findCard(b, id) !== null && (to !== "doing" || b.doing.length < b.wipLimit),
                              cardsIn(r, to).some((c) => c.id === id)));
// setWipLimit
ensures((r: Board) => implies(limit >= 1 && limit >= b.doing.length, r.wipLimit === limit));
```

```
$ vreact synth src/model.ts --write
hole in addCard: Board   …
  13698 candidates tested in 23.8s
  no verified solution found up to size 9: write this one by hand (or strengthen the spec)
hole in deleteCard: Board   scope: b, b.todo, b.doing, b.done, b.nextId, b.wipLimit, id
  candidate passes 400 random tests: removeEverywhere(b, id)
  28 candidates tested in 0.1s
  ✔ proved by Lean: removeEverywhere(b, id)
hole in moveCard: …   no verified solution found …
hole in setWipLimit: … no verified solution found …
wrote src/model.ts
```

`deleteCard` is synthesized (and proved). The others need guarded updates,
which are beyond the synthesizer's grammar — we write them, and the verifier
checks them.

---

## Step 3 — Hand-written code, machine-checked

A first `moveCard` forgets the WIP limit:

```ts
const card = findCard(b, id);
if (card === null) return b;
const rest = removeEverywhere(b, id);
switch (to) {
  case "todo":  return { ...rest, todo: [...rest.todo, card] };
  case "doing": return { ...rest, doing: [...rest.doing, card] };   // ← no WIP check
  case "done":  return { ...rest, done: [...rest.done, card] };
}
```

```
$ vreact verify
  INCOMPLETE         moveCard
✗ src/model.ts:89:11  [postcondition] postcondition of moveCard: implies(wellFormed(b), wellFormed(r))
    │ `grind` failed
    │ case grind.2.2.2.2.2.2.2.2.1.1
    │ …
✗ NOT VERIFIED  11/12 obligations proved, 1 failed
```

Adding `if (rest.doing.length >= b.wipLimit) return b;` and the reducer:

```
$ vreact verify
  VERIFIED           boardReducer
  ✓ src/model.ts                             12/12
  ✓ src/reducer.ts                           2/2
✔ VERIFIED  14/14 obligations proved
```

The reducer is verified *modularly*: it only sees the contracts of
`addCard`/`moveCard`/…, which `vreact_contracts` instantiates at each call.

---

## Step 4 — The App, top-down, against trusted stubs

Write `App.tsx` for real, and give each child a **stub**: the props type and
the contract, marked `@trusted`:

```tsx
/** @trusted — stub: contract only, implementation pending */
export function ColumnView(props: ColumnViewProps) {
  requires(distinct(props.cards, (c) => c.id));                          // keys
  callbackRequires(props.onSelect, (id) => props.cards.some((c) => c.id === id));
  …
  return <div className="todo-stub">ColumnView</div>;
}
```

The App keeps three invariants, including one that depends on a three-level
contract chain (*the selected card always exists*):

```tsx
invariant(wellFormed(board));
invariant(query.length <= MAX_QUERY);
invariant(selected === null || allCards(board).some((c) => c.id === selected));
…
<ColumnView … onSelect={(id) => setSelected(id)}
             onDelete={(id) => { dispatch({ kind: "delete", id }); if (selected === id) setSelected(null); }} />
```

```
$ vreact verify
Components
  TRUSTED            ColumnView             src/components/ColumnView.tsx:16
  TRUSTED            AddCardForm            …
  TRUSTED            Stats / WipControl / Details …
  VERIFIED*          App                    src/App.tsx:13
App certificates (VReact.run_allInv instantiated)
  VERIFIED*          VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound,
                     VTS.components.ColumnView.ColumnView.renderTrusted, …
  ✓ src/App.tsx                              25/25
VERIFIED* = all own obligations proved; relies on the contracts of the trusted declarations above
✔ VERIFIED modulo @trusted declarations  39/39 obligations proved
```

All 25 App obligations hold **relative to the stubs' contracts**; the
certificate lists precisely which assumptions remain. Among them: deleting the
selected card clears the selection; selecting an id from a column keeps
`selected` valid because `ColumnView` promises to report only ids it shows
(and the shown cards are a filter of the board's); the `ColumnView` keys
precondition follows from `wellFormed(board)`.

---

## Step 5 — Implement the children (and let the verifier catch the bugs)

Replacing the stubs with first drafts that contain three realistic bugs:

* `Stats`: `const pct = idiv(props.done * 100, total);` — no empty-board guard;
* `CardView`: the → button always moves to `"done"`;
* `AddCardForm`: `props.onAdd(draft, points)` — untrimmed, possibly empty.

```
$ vreact verify
✗ src/components/AddCardForm.tsx:20:9  [callback-contract] callback contract of onAdd(draft, points)
✗ src/components/CardView.tsx:28:75   [callback-contract] callback contract of onMove(props.card.id, right)
✗ src/components/Stats.tsx:9:15       [nonzero-divisor] divisor total is non-zero
    │ total : Int := props.todo + props.doing + props.done
    │ hpre : (0 ≤ props.todo ∧ 0 ≤ props.doing) ∧ 0 ≤ props.done
    │ h : props.doing + props.done + props.todo = 0
✗ NOT VERIFIED  41/79 obligations proved, 3 failed, 35 unchecked
```

Each failure points at the exact TypeScript expression, with the Lean goal
explaining it (for `Stats`: the empty board). The fixes:

```tsx
const pct = total === 0 ? 0 : idiv(props.done * 100, total);                    // Stats
const right: ColumnId | null = props.col === "todo" ? "doing" : props.col === "doing" ? "done" : null; // CardView
const title = draft.trim(); … if (title.length === 0) return; props.onAdd(title, points);           // AddCardForm
```

(`AddCardForm`'s proof also uses that `trim` never lengthens a string — a lemma
of the exact UTF-16 string model.)

---

## Step 6 — Done

```
$ vreact verify
Components
  VERIFIED           CardView               src/components/CardView.tsx:14
  VERIFIED           ColumnView             src/components/ColumnView.tsx:17
  VERIFIED           AddCardForm            src/components/AddCardForm.tsx:8
  VERIFIED           Stats                  src/components/Stats.tsx:6
  VERIFIED           WipControl             src/components/WipControl.tsx:6
  VERIFIED           Details                src/components/Details.tsx:5
  VERIFIED           App                    src/App.tsx:13
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             12/12
  ✓ src/reducer.ts                           2/2
  ✓ src/components/CardView.tsx              10/10
  ✓ src/components/ColumnView.tsx            10/10
  ✓ src/components/AddCardForm.tsx           7/7
  ✓ src/components/Stats.tsx                 3/3
  ✓ src/components/WipControl.tsx            6/6
  ✓ src/components/Details.tsx               4/4
  ✓ src/App.tsx                              25/25
✔ VERIFIED  79/79 obligations proved; components: 7/7 verified  (19.3s)
```

`App.certificate` states: *for every sequence of user events, effect flushes and
timer firings, every mounted component instance satisfies its invariant* — so
the board is always well-formed (unique ids, valid cards, WIP limit respected),
the selection always names an existing card, the inputs never exceed their
limits, no render ever indexes out of bounds or divides by zero, all keys are
distinct, and every callback is invoked within its contract.

```bash
npm run dev      # the same, unmodified .tsx runs in the browser
```

---

## Recap of the method

| need | tool |
|------|------|
| say what the code must do | `requires` / `ensures` / `invariant` / `callbackRequires` |
| find out whether the spec says enough | `vreact synth` (a spec satisfied by `return b` is too weak) |
| fill in straight-line code | `hole<T>()` + `vreact synth --write` |
| verify a parent before its children exist | `/** @trusted */` stubs with contracts |
| keep proofs small and fast | `/** @opaque */` + `ensures` (modular reasoning) |
| know exactly what is assumed | the certificate's `#print axioms` |
| when automation is not enough | `assert(…)` hints, or lemmas in `proofs/<Module>.lean` |
