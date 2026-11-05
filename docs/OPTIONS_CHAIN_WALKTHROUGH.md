# Walkthrough: building a verified options chain

This walkthrough builds `examples/options-chain`, a medium-complexity trading widget, with
vreact from an empty folder to a **fully verified** React app. The result has 6 components,
46 functions (the reducer among them) and 129 proof obligations. Its whole-app certificate
depends only on Lean's three standard axioms.

It is written for a developer who knows React and TypeScript but has never used formal
verification. Each new idea is explained the first time it appears. Every tool output below
comes from a real run. The raw logs are in [`options-chain/`](options-chain/), and a full
snapshot of `src/` at each step is in [`options-chain/steps/`](options-chain/steps/).
[`options-chain/replay.sh`](options-chain/replay.sh) re-runs every step and checks that the tool
still says the same thing.

> **Inspiration.** The feature set is modelled on the *Options Chain (new)* widget in the
> Trading Technologies documentation
> ([widget display](https://library.tradingtechnologies.com/trade/options/options-chain/description-options-chain/options-chain-new-widget-display/)).
> The component built here is an original, generic one. It is not that product and copies
> none of its branding, names or styling. The underlying "DIX" contract and all prices are
> made up.

---

## Contents

0. [What we build](#0-what-we-build)
1. [Setup](#1-setup)
2. [Step 1: the model, spec first](#step-1-the-model-spec-first)
3. [Step 2: the reducer](#step-2-the-reducer)
4. [Step 3: the chain, top-down against trusted stubs](#step-3-the-chain-top-down-against-trusted-stubs)
5. [Step 4: an invariant that depends on props](#step-4-an-invariant-that-depends-on-props)
6. [Step 5: the children, one by one](#step-5-the-children-one-by-one)
7. [Step 6: the App and a moving market](#step-6-the-app-and-a-moving-market)
8. [Step 7: final checks](#step-7-final-checks)
9. [What exactly is proven](#what-exactly-is-proven)
10. [Where the tool pushed back](#where-the-tool-pushed-back)
11. [Try it yourself](#try-it-yourself)
12. [The steps and their logs](#the-steps-and-their-logs)

---

## 0. What we build

An options chain shows the calls and puts of several expiries of one product, strike by strike,
around the price of the underlying futures contract. The finished widget looks like this
(a text sketch with illustrative numbers; the real one is an HTML table):

```
 [DEC 26] [MAR 27] [JUN 27]   [Collapse all]   Strikes ± [3] 7 11 99 All   Heat 1 ticks [−][+]
 ───────────── Calls ─────────────  Strike  ───────────── Puts ──────────────   Vol
  Qty   Bid     Ask     Qty                  Qty   Bid     Ask     Qty
 ▾ DIX DEC 26                        🔒       62    102.40  102.45  56            live
  102   3.60    3.95    79           99.00   145   2.65    2.95    20           21.9%
  …                                 102.00 ← the at-the-money row, highlighted
 ▸ DIX MAR 27                        🔓       84    103.10  103.15  25     held 103.10
 ┌ Buy DIX DEC 26 102.00 C ───────────────────────────────┐
 │ Quantity [−] 1 [+] [1][5][10][25]   Price [−] 3.10 [+]  │
 │ Market 2.95 / 3.10       [Submit] [Cancel]             │
 └────────────────────────────────────────────────────────┘
 Working orders: Buy 5 DIX DEC 26 102.00 C @ 3.10 [Cancel]
```

### Feature mapping

| Feature of the inspiration | Here | Where |
|---|---|---|
| Expiry buttons that jump to the expiry's ATM strike | one button per expiry: it expands the expiry, locks it to the futures price, focuses it, and scrolls to its at-the-money row (`href="#atm-<id>"`) | `OptionsChain.tsx`, `jump` in `reducer.ts` |
| Term row: symbol, expiry, best bid/ask of the futures | `TermRow`; the futures bid/ask are clickable | `TermRow.tsx` |
| Lock icon: chain locked to the underlying price | 🔒 = the strike window follows the live futures price; click to **hold** it at the price of that moment (🔓); click again to lock it to the live price again | `holdAt` / `follow` in `reducer.ts` |
| Expand/collapse per expiry and for all expiries | ▾/▸ in the term row; "Collapse all" / "Expand all" | `toggle`, `setCollapsed` |
| Quick strike filter 3, 7, 11, 99, All | strikes within N rows of the ATM row, per expiry | `strikeWindow` in `model.ts` |
| Rows: call market, strike in the middle, put market, volatility | `StrikeRow`; in-the-money cells shaded; the ATM row highlighted | `StrikeRow.tsx` |
| Heat map: approach / slight cross / larger cross, within a number of ticks | `heatOf`: `near` (blue), `cross` (light yellow), `deep` (dark yellow); threshold 1–5 ticks | `model.ts`, `styles.css` |
| Click a bid/ask (option or futures) to open a pre-filled order entry | `OrderTicket`: clicking a bid prepares a sell at the bid, an ask a buy at the ask; quantity and price adjustable; shows the live market and warns when the order would trade at once | `OrderTicket.tsx` |
| (orders) | working orders listed under the chain, each cancellable | `place` / `cancel` |

**Out of scope.** The following are not built:

* **Greeks and theoretical pricing.** Theoretical values and volatilities are *input data*.
  The demo values were computed once, offline, with Black-76 and pasted as constants. Nothing
  about pricing is verified.
* **Option spreads** (the optional stretch goal). Not built.
* **The expiry selector itself.** Choosing which expiries are in the chain is the parent's job:
  the chain shows the expiries it is given, each with a button.
* **Real trading.** No order routing. "Working orders" are kept in the component's state.
* **A real market feed.** The App simulates one: a timer moves the futures prices. Option quotes
  stay fixed in the demo.

### Prices are integers

Every price in the model is an `int`: a number of **ticks**. The demo tick is 0.05, so 102.40 is
2048. Why not `number`? A `number` is an IEEE double: `0.1 + 0.2 !== 0.3`. vreact models it
faithfully as a float, and that is exactly why proofs cannot reason about its values. Exchange
prices are tick-based anyway. A missing quote (no bid, no ask) is `null`, so a quote side has
type `int | null`. Volatility is an `int` in basis points, used for display only.

---

## 1. Setup

From a fresh clone (Node ≥ 22.6, Lean 4 via [elan](https://github.com/leanprover/elan)):

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain   # npm deps + Lean library
cd examples/options-chain
npx vreact verify          # ✔ VERIFIED 129/129
npm run dev                # the same .tsx files, running in React 18
```

The app was created by copying the setup of `examples/cart`: `package.json`, `tsconfig.json`
(`"strict": true`, `"lib": ["ES2023", "DOM"]`), `vite.config.ts`, `index.html`, a `.gitignore`
with `.vreact/`, and `vreact.json`:

```json
{ "src": "src", "exclude": ["main.tsx"], "proofs": "proofs", "out": ".vreact" }
```

`main.tsx` only mounts `<App/>`. It stays outside the verified program. In this walkthrough
the app's `node_modules` was a symlink to `../kanban/node_modules`, and the commands were run as
`node <repo>/vreact/bin/vreact.js …`. `npx vreact …` is the same program.

The finished app has seven verified files:

| file | what |
|---|---|
| `src/model.ts` | types, the chain's data requirements, ATM strike, strike window, ITM test, heat map, order validation, formatting |
| `src/reducer.ts` | the UI state, its invariant, the operations, the reducer |
| `src/OptionsChain.tsx` | the chain component |
| `src/TermRow.tsx` | one expiry's header row |
| `src/StrikeRow.tsx` | one strike row, and `PriceCell` (a clickable bid/ask cell) |
| `src/OrderTicket.tsx` | the order entry |
| `src/App.tsx` | the demo data and the simulated futures feed |

---

## Step 1: the model, spec first

### 1a. Contracts before code ([log](options-chain/01-model-spec.txt), [snapshot](options-chain/steps/01-model-spec/src/))

We start with the data types and with **contracts**: machine-checked statements of what a
function needs (`requires`, its *precondition*) and what it promises (`ensures`, its
*postcondition*). The bodies we do not know yet are left as `hole<T>()`, a placeholder that the
synthesizer will try to fill.

```ts
export type Quote = { readonly bid: int | null; readonly bidQty: int; readonly ask: int | null; readonly askQty: int };
export type Strike = { readonly strike: int; readonly call: Quote; readonly put: Quote;
                       readonly callTheo: int; readonly putTheo: int; readonly vol: int };
export type Expiry = { readonly id: int; readonly symbol: string; readonly label: string;
                       readonly future: Quote; readonly strikes: readonly Strike[] };

/** What the chain needs from its data: distinct expiry ids, distinct strikes in each expiry. */
export function validChain(es: readonly Expiry[]): boolean {
  return distinct(es, (e) => e.id) && es.every((e) => distinct(e.strikes, (s) => s.strike));
}

/**
 * `s` is a nearest strike to `price`: no strike of the ladder is strictly nearer.
 * A specification predicate, `@opaque`: proofs use it as one fact and never unfold it.
 * @opaque
 */
export function nearest(ks: readonly Strike[], s: Strike, price: int): boolean {
  return ks.every((t) => dist(s.strike, price) <= dist(t.strike, price));
}

/** The at-the-money row: the index of a nearest strike, or -1 for "none". */
export function atmIndex(ks: readonly Strike[], price: int): int {
  ensures((r: int) => -1 <= r && r < ks.length);
  ensures((r: int) => implies(r >= 0, nearest(ks, ks[r], price)));
  return hole<int>();
}

/** The rows of a ladder of n strikes that the filter shows around the ATM row. */
export function strikeWindow(n: int, atm: int, levels: int): Span {
  requires(0 <= atm && atm < n && levels >= 0);
  ensures((r: Span) => 0 <= r.lo && r.lo <= atm && atm < r.hi && r.hi <= n);
  ensures((r: Span) => forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, levels)));
  return hole<Span>();
}
```

`inWindow(i, atm, levels)` is `atm - levels <= i && i <= atm + levels`: the filter "3" shows the
ATM row and 3 rows on each side. `heatOf` gets four `ensures`, one per colour, each saying
exactly when the cell has that colour in terms of `edge` (by how many ticks the theoretical
value has crossed the cell's price). `midPrice` gets a contract too.

`@opaque` (the tag in the doc comment of `nearest`) tells vreact that proofs elsewhere should see only
the function's name and contract, not its body. For a specification predicate like `nearest`,
that is what we want: it stays one fact instead of being unfolded into a loop over the ladder.

```
$ vreact verify
translated 1 module(s), 6 proof obligation(s) → .vreact/ ; checking with Lean…
Functions
  VERIFIED           validChain
  …
  INCOMPLETE         quotePrice
  INCOMPLETE         midPrice
  …
  INCOMPLETE         atmIndex
  …
pending (hole() / sorry): quotePrice, midPrice, atmIndex, strikeWindow, heatOf

◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)  6/6 obligations proved; components: 0/0 verified  (2.5s)
```

A **proof obligation** is one claim that must be true for the program to be correct, such as
"this index is in bounds" or "this function returns what its `ensures` says". `vreact verify`
translates the code to Lean 4 and asks Lean to prove every obligation. A function is
`VERIFIED` when all of its obligations are proved, and `INCOMPLETE` while it still has a hole.

### 1b. Let the synthesizer test the spec ([log](options-chain/02-model-synth.txt))

`vreact synth` enumerates small programs, smallest first. It runs each one as JavaScript on
random inputs against the contracts, and asks Lean to prove the ones that pass.

```
$ vreact synth src/model.ts
hole 2/2 in quotePrice (with hole 1 = q.bid): int | null   scope: q, q.bid, q.bidQty, q.ask, q.askQty, side
  candidate passes 400 random tests: q.ask   (2 candidate(s) tested in 0.0s)
  ✔ proved by Lean: quotePrice with q.bid / q.ask
hole in midPrice: int | null   scope: q, q.bid, q.bidQty, q.ask, q.askQty
  candidate passes 400 random tests: q.bid   (1 candidate(s) tested in 0.0s)
  ✔ proved by Lean: q.bid
hole in atmIndex: int   scope: ks, price
  26743 candidates tested in 60.0s, up to size 7; stopped: the 60s time limit was reached at size 7
  no verified solution for hole in atmIndex: no candidate passed the tests
  most common failure (26743×): price: postcondition fails on [[],7] ↦ 7
…
```

`quotePrice` is filled as expected. The `midPrice` result is a warning: **`return q.bid`
satisfies its contract.** The first contract only said "null when both sides are missing" and
"within the spread", and the bid is within the spread. A verified function is only as good as
its specification, and the synthesizer just showed that ours does not say "mid".

For `atmIndex`, no candidate passed, not even the trivial `-1`. The reason is how synth tests:
it runs the contracts as JavaScript, where `implies(a, b)` is an ordinary function call that
evaluates `b` even when `a` is false. For `r = -1`, `ks[-1].strike` throws. In Lean, `implies`
is guarded. We write the same condition with `||`, which short-circuits in both languages
([log](options-chain/03-model-synth-guard.txt)):

```ts
ensures((r: int) => r < 0 || nearest(ks, ks[r], price));
```

```
$ vreact synth src/model.ts
…
hole in atmIndex: int   scope: ks, price
  candidate passes 400 random tests: 0 - 1   (7 candidate(s) tested in 0.0s)
  ✔ proved by Lean: 0 - 1
```

Now synth proves that **`return -1` ("never an ATM row") satisfies the spec**. A second weak
spec. Both are fixed by saying what we mean ([log](options-chain/04-model-synth-strong.txt)):

```ts
// midPrice: the mid, rounded down, of a two-sided market; otherwise the side that is there
ensures((r: int | null) => isMid(q, r));        // isMid: r === idiv(bid + ask, 2) when both exist
ensures((r: int | null) => q.ask !== null || r === q.bid);
ensures((r: int | null) => q.bid !== null || r === q.ask);
ensures((r: int | null) => withinSpread(q, r)); // kept: a property the proof must also establish

// atmIndex: "-1 for none" must not be an escape hatch
ensures((r: int) => implies(ks.length > 0, r >= 0));
```

```
$ vreact synth src/model.ts --write
…
  ✔ proved by Lean: quotePrice with q.bid / q.ask
hole in midPrice: int | null   …
  no verified solution for hole in midPrice: no candidate passed the tests
  most common failure (11824×): q.bid: postcondition fails on [{"bid":null,"bidQty":3,"ask":10,"askQty":3}] ↦ null
…
wrote src/model.ts
```

`q.bid` is now refuted by a concrete input (no bid, an ask of 10). The rest needs branches,
which synth does not build ("write this one by hand"). `--write` keeps the one proved fill.

### 1c. Hand-written code, machine-checked ([log](options-chain/05-model-bugs.txt), [snapshot](options-chain/steps/05-model-bugs/src/model.ts))

The first hand-written `atmIndex` is the obvious fast version for an ascending ladder, and the
window is written from memory:

```ts
// the ladder is ascending: take the first strike at or above the price,
// or the one just below it if that one is nearer
const k = ks.findIndex((s) => s.strike >= price);
return price - ks[k - 1].strike <= ks[k].strike - price ? k - 1 : k;
…
return { lo: Math.max(0, atm - levels), hi: Math.min(n, atm + levels) };   // strikeWindow
```

```
$ vreact verify
…
✗ src/model.ts:119:11  [postcondition] postcondition of atmIndex: r < 0 || nearest(ks, ks[r], price)
    │ vreact: (deterministic) timeout: the automation did not finish within this obligation's budget …
✗ src/model.ts:121:11  [postcondition] postcondition of atmIndex: implies(ks.length > 0, r >= 0)
    │ vreact_auto could not prove the goal (grind stopped at Lean's recursion limit)
    │ …
✗ src/model.ts:125:18  [index] index k - 1 is within bounds of ks
    │ `grind` failed
    │ k : Int := JS.findIndex ks fun s => JS.le price s.strike
    │ …
    │ h_1 : (JS.findIndex ks fun s => JS.le price s.strike) = -1
    │ right : ∀ (x : Strike), x ∈ ks → JS.le price x.strike = false
    │ ⊢ False
✗ src/model.ts:125:38  [index] index k is within bounds of ks
    │ h : (JS.findIndex ks fun s => JS.le price s.strike) + 1 ≤ 0
    │ ⊢ False
✗ src/model.ts:139:11  [postcondition] postcondition of strikeWindow: 0 <= r.lo && r.lo <= atm && atm < r.hi && r.hi <= n
    │ h_pre : (0 ≤ atm ∧ atm < n) ∧ levels ≥ 0
    │ h : -1 * atm + min n (atm + levels) ≤ 0
    │ h_1 : ¬n + -1 * atm + -1 * levels ≤ 0
    │ ⊢ False
✗ src/model.ts:140:11  [postcondition] postcondition of strikeWindow: forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, leve…
✗ NOT VERIFIED  18/24 obligations proved, 6 failed; components: 0/0 verified  (38.3s)
```

How to read a failure: the lines above `⊢` are what Lean knows at that point (hypotheses), and
`⊢ False` means they were not enough. Often they *are* a counterexample:

* **`[index] k - 1` and `[index] k`: the ATM at the edges, a real bug.** The hypotheses say
  `findIndex … = -1` and "no strike is ≥ price": when the futures trade above the top strike,
  `k` is `-1` and `ks[k]` is read out of bounds. When the price is at or below the bottom strike,
  `k` is `0` and `ks[k - 1]` is out of bounds. In JavaScript both give `undefined`, then a
  `TypeError` in render. After a large move of the underlying, this is a realistic situation.
* **`strikeWindow`: an off-by-one, a real bug.** `h` and `h_1` together say
  `min(n, atm + levels) ≤ atm` while `atm + levels < n`, so `levels = 0`. With `levels = 0`, the
  window `[atm, atm)` is empty and the ATM row disappears. In general the last row
  `atm + levels` is missing: the filter "3" showed 3 rows below the ATM row but only 2 above.
  The fix is `hi: Math.min(n, atm + levels + 1)`.
* **The two `atmIndex` postconditions** are not about the edge bugs. Even with both edges
  guarded, this version's "nearest" proof needs two facts the automation does not have:
  that `findIndex` returns the *first* match (so every strike before `k` is below the price),
  and that "ascending" is transitive (so strikes far from `k` are farther away).

### 1d. Make the code easy to prove ([log](options-chain/06-model-search.txt), [log](options-chain/07-model-verified.txt))

Instead of teaching the prover those facts, we write `atmIndex` so that its correctness is
immediate: return the first strike that no other strike beats.

```ts
// the first strike that no other strike beats (O(n²) on a ladder of ~15 strikes)
return ks.findIndex((s) => nearest(ks, s, price));
```

There are no indices, so there are no edges. "The strike at the returned index satisfies the
predicate" is a known fact about `findIndex`, and it is exactly the postcondition. This is why
`nearest` is `@opaque`: the predicate in the code and the predicate in the contract are the same
atom. One obligation still fails:

```
✗ src/model.ts:121:11  [postcondition] postcondition of atmIndex: implies(ks.length > 0, r >= 0)
    │ `grind` failed
    │ h₂₁ : ↑ks.length > 0
    │ …
✗ NOT VERIFIED  21/22 obligations proved, 1 failed; components: 0/0 verified  (1.9s)
```

"A non-empty ladder has a nearest strike" is true. But proving it is an induction over the list
(a minimum exists), and the automation does not do induction. We state what is provable and
still rules out the escape hatch:

```ts
// whenever some strike is nearest, an ATM row is found.
// (A non-empty ladder always has one; the prover cannot show that without induction.)
ensures((r: int) => implies(ks.some((s) => nearest(ks, s, price)), r >= 0));
```

`return -1` is now refuted too (synth's random tests and Lean both reject it), and the chain
handles `-1` anyway (step 3).

```
$ vreact verify
…
  VERIFIED           atmIndex
  VERIFIED           inWindow
  VERIFIED           strikeWindow
  …
  VERIFIED           heatOf
  …
  ✓ src/model.ts                             22/22

✔ VERIFIED  22/22 obligations proved; components: 0/0 verified  (3.1s)
```

`heatOf` and `midPrice` were right the first time. The verifier checked, for example, that
`idiv(b + a, 2)` always lies between bid and ask when `b ≤ a`.

---

## Step 2: the reducer

The UI state lives in one record, managed by `useReducer`. Its **invariant** is a property that
must hold in *every* state the component can ever reach. Here it says that the heat threshold
is valid and that every working order is valid, with distinct ids below `nextId`:

```ts
export type ChainUi = {
  readonly collapsed: readonly int[]; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly held: readonly Hold[];     // unlocked expiries: { expiry, price captured when unlocked }
  readonly focus: int | null;         // the expiry last jumped to
  readonly heat: int;                 // heat-map threshold, in ticks
  readonly orders: readonly Order[];  // working orders
  readonly nextId: int;
};

export function wellFormed(u: ChainUi): boolean {
  return 1 <= u.heat && u.heat <= MAX_HEAT &&
    distinct(u.orders, (o) => o.id) &&
    u.orders.every((o) => validOrder(o) && o.id < u.nextId);
}
```

A reducer must be **total**: no `requires`. React may apply an action to any queued state, so
every operation must keep the invariant from any well-formed state, and say so:
`ensures((r) => implies(wellFormed(u), wellFormed(r)))`. Each operation is `@opaque`, so the
reducer and the components reason with the contracts only. The reducer is a `switch` over a
discriminated-union `Action` (one variant per operation) that delegates to them.

### 2a. Synthesis finds two weak specs ([log](options-chain/08-reducer-synth.txt))

```
$ vreact synth src/reducer.ts
hole in setCollapsed: ChainUi   …
  ✔ proved by Lean: { ...u, collapsed: ids }
hole in setFilter: ChainUi   …
  ✔ proved by Lean: { ...u, filter: f }
hole in holdAt: ChainUi   …
  untested candidate: chainReducer(u, { kind: "follow", expiry: u.heat })
  ✗ chainReducer(u, { kind: "follow", expiry: u.heat }): does not translate: src/reducer.ts:70:1: mutually recursive declarations are not supported
  …
hole in follow: ChainUi   …
  candidate passes 400 random tests: jump(u, id)   (17 candidate(s) tested in 0.1s)
  ✔ proved by Lean: jump(u, id)
…
hole in cancel: ChainUi   …
  candidate passes 400 random tests: u   (1 candidate(s) tested in 0.0s)
  ✔ proved by Lean: u
```

* `cancel` (contract: keeps the invariant) is satisfied by **doing nothing**.
* `follow` (contract: afterwards the expiry follows the futures price) is satisfied by
  **`jump(u, id)`**, which also expands the expiry and moves the focus. The contract never said
  that everything else stays the same. That missing part is called a **frame condition**.

We add the frame conditions as predicates and the missing functional postcondition for
`cancel`:

```ts
/** Frame condition: the same expiries are collapsed, same filter, focus and heat threshold. */
export function sameView(u: ChainUi, r: ChainUi): boolean { … }
/** Frame condition: every hold of another expiry than `id` is kept. */
export function keepsHolds(u: ChainUi, r: ChainUi, id: int): boolean { … }

// holdAt and follow
ensures((r: ChainUi) => sameView(u, r) && keepsHolds(u, r, id));
// cancel
ensures((r: ChainUi) => !r.orders.some((o) => o.id === id));
ensures((r: ChainUi) => u.orders.every((o) => o.id === id || r.orders.some((p) => p.id === o.id)));
```

### 2b. A synth limitation, and how to work around it ([log](options-chain/09-reducer-synth-strong.txt), [log](options-chain/10-reducer-synth-ops.txt))

With the stronger specs, synth gave up on every remaining hole:

```
hole in cancel: ChainUi   …
  no generated input can test this hole (400 of 400 reach another unfilled hole): the smallest candidates are checked by Lean only
  untested candidate: chainReducer(u, { kind: "follow", expiry: u.heat })
  ✗ chainReducer(u, { kind: "follow", expiry: u.heat }): does not translate: src/reducer.ts:144:1: mutually recursive declarations are not supported
  …
  no verified solution for hole in cancel: no generated input can test this hole (400 of 400 reach another unfilled hole)
```

Synth offers every total function of the module as a building block, including `chainReducer`,
which calls the very operation being synthesized. Those candidates cannot be tested or
translated, and the search stops after three of them, before it reaches the `filter`
candidates. The workaround follows the natural order anyway: **synthesize the operations
before writing the reducer that calls them.** With `chainReducer` removed for one run
([snapshot](options-chain/steps/10-reducer-synth-ops/src/reducer.ts)):

```
$ vreact synth src/reducer.ts --write
…
hole in follow: ChainUi   …
  candidate passes 400 random tests: { ...u, held: u.held.filter((x) => x.expiry !== id) }   (10409 candidate(s) tested in 24.9s)
  ✔ proved by Lean: { ...u, held: u.held.filter((x) => x.expiry !== id) }
…
hole in cancel: ChainUi   …
  candidate passes 400 random tests: { ...u, orders: u.orders.filter((x) => x.id !== id) }   (13940 candidate(s) tested in 42.0s)
  ✔ proved by Lean: { ...u, orders: u.orders.filter((x) => x.id !== id) }
wrote src/reducer.ts
```

Both are the intended programs. With the frame conditions in place, synth's answer is the
right one.

### 2c. The rest by hand ([log](options-chain/11-reducer-bug.txt), [log](options-chain/12-reducer-verified.txt))

`holdAt` puts the new hold first (because `heldPrice` reads the first hold of an expiry).
`place` validates and appends:

```ts
if (!validQty(qty) || price <= 0) return u;
const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike,
                   buy: t.side === "ask", qty: qty, price: price };
return { ...u, orders: [...u.orders, o] };
```

```
$ vreact verify
…
✗ src/reducer.ts:136:11  [postcondition] postcondition of place: implies(wellFormed(u), wellFormed(r))
    │ h_2 :
    │   x ∈ u.orders ∨
    │     x =
    │       { id := u.nextId, expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.ask,
    │         qty := qty, price := price }
    │ h_6 : -1 * x.id + u.nextId ≤ 0
✗ NOT VERIFIED  43/44 obligations proved, 1 failed; components: 0/0 verified  (6.4s)
```

The counterexample is the new order `x` itself, whose id is `u.nextId`: `nextId` was never
advanced, so the next order would reuse the id. The fix is `nextId: u.nextId + 1`:

```
✔ VERIFIED  44/44 obligations proved; components: 0/0 verified  (8.0s)
```

---

## Step 3: the chain, top-down against trusted stubs

We write the parent for real before its children exist. Each child is a **trusted stub**: its
props type and its contract, a placeholder body, and `@trusted`. `@trusted` means "do not verify
this body, assume the contract". vreact then verifies the parent *relative to* the children's
contracts, and reports exactly what is assumed.

```tsx
/** One strike: call market | strike | put market | volatility.
 *  Clicking a bid or an ask reports exactly the price shown in that cell.
 *  @trusted — stub: contract only, implementation pending */
export function StrikeRow(props: StrikeRowProps) {
  requires(props.heat >= 1);
  callbackRequires(props.onPick, (right, side, price) => quotePrice(legOf(props.strike, right), side) === price);
  return <tr className="todo-stub"><td>StrikeRow</td></tr>;
}
```

`requires` on a component is what every parent must establish for its props: here, a valid
heat threshold. `callbackRequires` is the child's promise about the arguments it passes to a
callback prop: `onPick` is only ever called with the price shown in the clicked cell. The parent
may rely on it, and the child is checked against it. `TermRow` promises the same for the futures
prices, and `OrderTicket` promises to submit only valid orders
(`callbackRequires(props.onSubmit, (qty, price) => validQty(qty) && price > 0)`).

The chain itself, first version ([snapshot](options-chain/steps/14-chain-atm-edge/src/OptionsChain.tsx)),
in its essentials:

```tsx
export function OptionsChain(props: OptionsChainProps) {
  requires(validChain(props.expiries));
  const [ui, dispatch] = useReducer(chainReducer, INITIAL_UI);
  const [ticket, setTicket] = useState<Ticket | null>(null);
  invariant(wellFormed(ui));
  invariant(ticket === null || ticket.price > 0);
  const levels = levelsOf(ui.filter);
  …
  {props.expiries.map((e) => {
    const live = midPrice(e.future);
    const held = heldPrice(ui.held, e.id);
    const center: int | null = held === null ? live : held;   // locked: live price; unlocked: held price
    const n = e.strikes.length;
    const atm = center === null ? -1 : atmIndex(e.strikes, center);
    const span: Span = levels === null ? { lo: 0, hi: n } : strikeWindow(n, atm, levels);
    const rows = e.strikes.slice(span.lo, span.hi);
    …
    return (
      <tbody key={e.id}>
        <TermRow expiry={e} open={open} held={held} focused={ui.focus === e.id}
          onLock={() => {
            if (held !== null) dispatch({ kind: "follow", expiry: e.id });
            else if (live !== null) dispatch({ kind: "hold", expiry: e.id, price: live });
          }}
          onPick={(side, price) => { if (price > 0) setTicket({ expiry: e.id, leg: "future", strike: 0, side: side, price: price }); }}
          … />
        {open && rows.map((s) => (
          <StrikeRow key={s.strike} strike={s} price={live} heat={ui.heat} …
            onPick={(right, side, price) => {
              if (price > 0) setTicket({ expiry: e.id, leg: legFor(right), strike: s.strike, side: side, price: price });
            }} />
        ))}
      </tbody>
    );
  })}
```

Two quick rejections came first. VTS does not accept an enum as a React key
([log](options-chain/13-chain-key-rejected.txt)): `✗ VTS src/OptionsChain.tsx:63:26: keys must be
int or string`, so the filter buttons use `key={filterLabel(f)}`. It also did not unify a
ternary whose branches are `int | null` and a narrowed `int`
([log](options-chain/13b-chain-ternary-rejected.txt)): `✗ VTS src/OptionsChain.tsx:98:42: type
mismatch: expected int, got int | null`. The annotation `const center: int | null` above fixes
that. Then the first real result ([log](options-chain/14-chain-atm-edge.txt)):

```
$ vreact verify
…
✗ src/OptionsChain.tsx:101:67  [precondition] precondition of strikeWindow(n, atm, levels)
    │ `grind` failed
    │ …
    │ center : Option Int :=
    │   match h₈ : held with
    │   | some held_1 => some held_1
    │   | none => live
    │   …
✗ NOT VERIFIED  69/75 obligations proved, 2 failed, 4 unchecked; components: 0/5 verified  (30.0s)
```

This is the **ATM at the edge, one level up**. `strikeWindow` requires `0 <= atm`, but `atm` is
`-1` when the ladder is empty or when there is no price at all (no bid, no ask, nothing held).
The fix is the first condition below:

```tsx
// no ATM row (empty ladder, or no price at all) or "All": show every strike
const span: Span = atm < 0 || levels === null ? { lo: 0, hi: n } : strikeWindow(n, atm, levels);
```

([log](options-chain/15-chain-topdown.txt))

```
$ vreact verify
Components
  TRUSTED            TermRow                src/TermRow.tsx:19
  TRUSTED            StrikeRow              src/StrikeRow.tsx:18
  TRUSTED            OrderTicket            src/OrderTicket.tsx:15
  VERIFIED*          OptionsChain           src/OptionsChain.tsx:31
  VERIFIED*          App                    src/App.tsx:79
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED*          VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound, VTS.OrderTicket.OrderTicket.init_inv, VTS.OrderTicket.OrderTicket.renderTrusted, VTS.OrderTicket.OrderTicket.stable, VTS.StrikeRow.StrikeRow.init_inv, VTS.StrikeRow.StrikeRow.renderTrusted, VTS.StrikeRow.StrikeRow.stable, VTS.TermRow.TermRow.init_inv, VTS.TermRow.TermRow.renderTrusted, VTS.TermRow.TermRow.stable
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           22/22
  ✓ src/OptionsChain.tsx                     26/26
  ✓ src/App.tsx                              5/5

trusted (not verified, contracts assumed): TermRow, StrikeRow, OrderTicket
VERIFIED* = all own obligations proved; relies on the contracts of the trusted declarations above

✔ VERIFIED modulo @trusted declarations  75/75 obligations proved; components: 0/5 verified  (11.6s)
```

**`VERIFIED*`** means that all of the component's own obligations are proved, assuming the
contracts of the `@trusted` stubs. A component needs a root to run in, so at this step `App.tsx`
is a minimal root: the demo data and `<OptionsChain expiries={EXPIRIES} />`.

The **certificate** is a theorem vreact generates for each root component. It instantiates the
soundness theorem of vreact's React model (`VReact.run_allInv`) for this app: *for every
sequence of user events, effect runs and timer firings, every mounted component satisfies its
invariant.* Lean's `#print axioms` then lists everything the theorem rests on. `propext`,
`Classical.choice` and `Quot.sound` are Lean's three standard axioms. The other nine names are
the stubs' assumptions: for each stub, that it renders as its contract says (`renderTrusted`),
that it starts in a state satisfying its invariant (`init_inv`), and that its invariant survives
new props (`stable`). Nothing unverified is hidden: to finish, those names must disappear.

Among the 26 chain obligations: every list key is distinct (expiry ids and strikes from
`validChain`, and the rows are a `slice` of the strikes), `StrikeRow`'s precondition `heat >= 1`
follows from the invariant, `e.strikes[liveAtm]` is in bounds, and each callback keeps the
chain's invariant. For example, a picked price must be positive before it becomes a ticket,
hence the `if (price > 0)`.

The demo data in `App.tsx` is an `@opaque` constant with a module-level fact:

```ts
/** @opaque */
export const EXPIRIES: readonly Expiry[] = [ /* 3 expiries × 14 strikes */ ];
// a fact about the constant, proved once by evaluation and then available to every proof
assert(validChain(EXPIRIES));
```

`@opaque` keeps the 42 records out of every goal. The `assert` is proved once, by evaluating
it, and the chain's precondition then follows from it.

---

## Step 4: an invariant that depends on props

The ticket should name its expiry ("DIX DEC 26 102.00 C") and show the contract's live market.
A natural first draft records the fact that "we only open tickets from listed expiries" as an
invariant, and relies on it ([snapshot](options-chain/steps/16-props-stability/src/OptionsChain.tsx)):

```tsx
// the ticket's contract belongs to a listed expiry (we only open tickets from listed ones)
invariant(ticket === null || props.expiries.some((e) => e.id === ticket.expiry));
…
const tExp = ticket === null ? undefined : props.expiries.find((e) => e.id === ticket.expiry);
…
<OrderTicket … title={`${tExp!.symbol} ${tExp!.label} ${contractText(ticket.leg, ticket.strike)}`}
               market={marketOf(tExp!, ticket)} />
```

([log](options-chain/16-props-stability.txt))

```
$ vreact verify
✗ src/OptionsChain.tsx:32:17  [props-stability] OptionsChain: invariant survives a re-render with new props (state is preserved)
    │ `grind` failed
    │ props props' : Props
    │ σ : State
    │ h :
    │   … ∧
    │       match σ.ticket with
    │       | some ticket => ∃ e, e ∈ props.expiries ∧ e.id = ticket.expiry
    │       | none => True
    │ h_1 :
    │   (List.map (fun e => e.id) props'.expiries).Nodup ∧
    │     ∀ (x : model.Expiry), x ∈ props'.expiries → (List.map (fun s => s.strike) x.strikes).Nodup
    │ …
✗ NOT VERIFIED  73/78 obligations proved, 1 failed, 4 unchecked; components: 0/5 verified  (16.7s)
```

The handlers do establish the invariant: the `tExp!` assertions and every `setTicket` were proved.
The failure is about something else. When the parent re-renders with new props, **React keeps
the component's state**. The goal shows the old `props` (where the ticket's expiry is listed) and
new props `props'` that only satisfy the precondition. Nothing stops the feed from dropping the
expiry, for example when it expires, while a ticket for it is open. An invariant that ties state
to props cannot survive that, and the verifier checks this case for every component
(the `[props-stability]` obligation).

The fix the skill recommends is to keep the invariant about state only, look the expiry up at
render time, and clamp ([log](options-chain/17-props-clamped.txt)):

```tsx
// the ticket's expiry, looked up in the current props: it may have been delisted meanwhile
const tExp = ticket === null ? undefined : props.expiries.find((e) => e.id === ticket.expiry);
…
{ticket !== null && tExp !== undefined && <OrderTicket … title={`${tExp.symbol} ${tExp.label} …`} market={marketOf(tExp, ticket)} />}
{ticket !== null && tExp === undefined && (
  <div className="ticket gone"><p>This contract is no longer listed.</p><button onClick={() => setTicket(null)}>Close</button></div>
)}
```

```
✔ VERIFIED modulo @trusted declarations  76/76 obligations proved; components: 0/5 verified  (8.6s)
```

The same reasoning is why the reducer's invariant says nothing about the expiries:
`collapsed` and `held` may name expiries that are gone, and the chain only looks them up.

---

## Step 5: the children, one by one

### 5a. StrikeRow ([log](options-chain/18-strikerow-bug.txt), [log](options-chain/19-strikerow.txt))

`StrikeRow.tsx` also gets `PriceCell`, one clickable bid or ask, whose contract is the smallest
possible promise:

```tsx
export function PriceCell(props: PriceCellProps) {
  callbackRequires(props.onPick, (p) => props.price === p);
  const p = props.price;
  const cls = props.itm ? "px itm" : "px";
  if (p === null) return <td className={cls}>–</td>;      // no quote: no button
  return <td className={`${cls} heat-${props.heat}`}><button onClick={() => props.onPick(p)}>{fmtPrice(p)}</button></td>;
}
```

`StrikeRow` renders four of them, two for the call and two for the put. Its own contract
(`quotePrice(legOf(strike, right), side) === price`) must follow from each cell's contract. The
first version had a copy-paste error that is easy to miss in a mirrored layout:

```tsx
<PriceCell price={s.put.bid} heat={heatOf("bid", s.put.bid, s.putTheo, t)} itm={putItm} onPick={(x) => props.onPick("put", "ask", x)} />
<PriceCell price={s.put.ask} heat={heatOf("ask", s.put.ask, s.putTheo, t)} itm={putItm} onPick={(x) => props.onPick("put", "ask", x)} />
```

```
$ vreact verify
✗ src/StrikeRow.tsx:55:110  [callback-contract] callback contract of onPick("put", "ask", x)
    │ `grind` failed
    │ hpre_1 : props.heat ≥ 1
    │ …
✗ NOT VERIFIED  66/98 obligations proved, 1 failed, 31 unchecked; components: 1/6 verified  (2.6s)
```

A **callback-contract** obligation says that a call of a callback prop satisfies its
`callbackRequires`. Line 55 is the put **bid** cell, which reports `"ask"`. Clicking a put's bid
would have opened a *buy* ticket at the *bid* price. After the fix (`"bid"`), `StrikeRow` and
`PriceCell` are `VERIFIED`, and everything that was `UNCHECKED` because it imported the failing
module is checked again: `✔ VERIFIED modulo @trusted declarations  98/98 obligations proved;
components: 2/6 verified`.

### 5b. TermRow and OrderTicket ([log](options-chain/20-children-bug.txt), [log](options-chain/21-children-verified.txt))

`TermRow` reuses `PriceCell` for the futures bid and ask, and verifies on the first try (12/12).
`OrderTicket` has its own state, initialised from the clicked cell, and an invariant over it:

```tsx
export function OrderTicket(props: OrderTicketProps) {
  requires(props.ticket.price > 0);
  callbackRequires(props.onSubmit, (qty, price) => validQty(qty) && price > 0);
  const [qty, setQty] = useState<int>(1);
  const [price, setPrice] = useState<int>(props.ticket.price);
  invariant(validQty(qty) && price > 0);
  …
  <button onClick={() => setPrice(price - 1)}>−</button>
```

```
$ vreact verify
✗ src/OrderTicket.tsx:46:17  [handler] onClick handler on <button> preserves the invariant of OrderTicket
    │ hinv : (1 ≤ σ.qty ∧ σ.qty ≤ 500) ∧ σ.price > 0
    │ h : σ.price + -1 ≤ 0
✗ NOT VERIFIED  90/122 obligations proved, 1 failed, 31 unchecked; components: 3/6 verified  (5.7s)
```

At a price of 1 tick, "−" makes it 0. A **handler** obligation says that a click, run against the
state the user saw, keeps the invariant. The counterexample is right there (`σ.price + -1 ≤ 0`).
The fix is a guard, and the button is disabled for good measure:

```tsx
<button disabled={price <= 1} onClick={() => { if (price > 1) setPrice(price - 1); }}>−</button>
```

```
Components
  VERIFIED           PriceCell              src/StrikeRow.tsx:12
  VERIFIED           StrikeRow              src/StrikeRow.tsx:37
  VERIFIED           TermRow                src/TermRow.tsx:19
  VERIFIED           OrderTicket            src/OrderTicket.tsx:19
  VERIFIED           OptionsChain           src/OptionsChain.tsx:32
  VERIFIED           App                    src/App.tsx:79
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound

✔ VERIFIED  122/122 obligations proved; components: 6/6 verified  (9.4s)
```

The submit button needs no guard: the invariant already makes `(qty, price)` valid, which is
what the `onSubmit` contract asks for. The quantity presets `[1, 5, 10, 25]` are checked
against the invariant too. One thing React does that the verifier does not care about: a ticket
keeps its state when another cell is clicked. The chain gives the ticket a `key` built from the
clicked cell, so a new cell remounts it with fresh values.

---

## Step 6: the App and a moving market

The App now simulates a feed: every 0.8 s, all futures prices move by −2..+2 ticks, staying
within ±40 ticks of the data. The chain receives new `expiries` props every tick, so the
props-stability work of step 4 matters now. First draft
([snapshot](options-chain/steps/22-app-stale-timer/src/App.tsx)):

```tsx
const [offset, setOffset] = useState<int>(0);
const [seed, setSeed] = useState<int>(1);
const [paused, setPaused] = useState<boolean>(false);
invariant(-MAX_MOVE <= offset && offset <= MAX_MOVE);
invariant(0 <= seed && seed < 65537);
useEffect(() => {
  if (paused) return;
  const id = setInterval(() => {
    const next = nextSeed(seed);
    const move = (next % 5) - 2;
    setSeed(next);
    if (-MAX_MOVE <= offset + move && offset + move <= MAX_MOVE) setOffset((o) => o + move);
  }, 800);
  return () => clearInterval(id);
}, [paused, seed, offset]);
const expiries = moveFutures(EXPIRIES, offset);
```

([log](options-chain/22-app-stale-timer.txt), full goal in
[22-app-stale-timer-full.txt](options-chain/22-app-stale-timer-full.txt))

```
$ vreact verify
✗ src/App.tsx:106:3  [effect-robust] timer callbacks of the effect preserve the invariant of App from any state
    │ `grind` failed
    │ hinv : (-40 ≤ σ.offset ∧ σ.offset ≤ 40) ∧ 0 ≤ σ.seed ∧ σ.seed < 65537
    │ …
✗ NOT VERIFIED  127/128 obligations proved, 1 failed; components: 5/6 verified  (9.4s)

$ vreact verify --full     # the same failure, complete goal (abridged here)
    │   t = fun x =>
    │     if -40 ≤ σ.offset + (… - 2) then
    │       if σ.offset + (… - 2) ≤ 40 then
    │         { updates := [ fun τ => { offset := τ.offset, seed := …, paused := τ.paused },
    │                        fun τ => { offset := τ.offset + (… - 2), seed := τ.seed, paused := τ.paused } ] }
```

The timer callback is a **stale closure**. Its guard reads `σ.offset` from the render that
created the timer, but its update `o => o + move` is applied to `τ`, the state React holds when
it processes the update. vreact's model (see `vreact/docs/SEMANTICS.md` §2.2) treats effects and
timers as running later, against any state that satisfies the invariant. So it asks for an
**effect-robust** update: one that keeps the invariant from *every* valid `τ`, not just from the
snapshot. With `τ.offset = 40` and `move = +2`, this one does not.

The fix the skill recommends: put the related state in one record, and make the timer apply one
total function to whatever state it finds ([log](options-chain/23-final.txt)):

```ts
export type Feed = { readonly offset: int; readonly seed: int };
export function validFeed(f: Feed): boolean {
  return -MAX_MOVE <= f.offset && f.offset <= MAX_MOVE && 0 <= f.seed && f.seed < 65537;
}
/** One tick of the feed: move by -2..+2 ticks, bouncing back at ±MAX_MOVE. Total. */
export function stepFeed(f: Feed): Feed {
  ensures((r: Feed) => implies(validFeed(f), validFeed(r)));
  const seed = nextSeed(f.seed);
  const move = (seed % 5) - 2;
  const next = f.offset + move;
  return { offset: next > MAX_MOVE || next < -MAX_MOVE ? f.offset - move : next, seed: seed };
}
…
const [feed, setFeed] = useState<Feed>({ offset: 0, seed: 1 });
invariant(validFeed(feed));
useEffect(() => {
  if (paused) return;
  const id = setInterval(() => setFeed((f) => stepFeed(f)), 800);
  return () => clearInterval(id);
}, [paused]);
```

Because the App now has a timer that sets state, its "Pause feed" click is checked as
**rebase-safe** (a `handler-rebased` obligation). React may render the click before a pending
timer update and then re-apply both, so the click must keep the invariant for *every* value of
`feed`, the field the timer writes. The other fields are as in the snapshot. The click writes
only `paused`, so this holds at once. A click that changed `feed` from the snapshot would have
to guard inside a functional update.

```
$ vreact verify
Components
  VERIFIED           PriceCell              src/StrikeRow.tsx:12
  VERIFIED           StrikeRow              src/StrikeRow.tsx:37
  VERIFIED           TermRow                src/TermRow.tsx:19
  VERIFIED           OrderTicket            src/OrderTicket.tsx:19
  VERIFIED           OptionsChain           src/OptionsChain.tsx:32
  VERIFIED           App                    src/App.tsx:115
Functions
  VERIFIED           validChain
  …
  VERIFIED           moveFutures
  VERIFIED           nextSeed
  VERIFIED           validFeed
  VERIFIED           stepFeed
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           22/22
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     27/27
  ✓ src/App.tsx                              12/12

✔ VERIFIED  129/129 obligations proved; components: 6/6 verified  (11.4s)
```

`moveFutures(EXPIRIES, offset)` maps over the constant, and its `ensures` (validity is preserved)
gives the chain its precondition on every tick.

---

## Step 7: final checks

* **Verification.** `✔ VERIFIED 129/129`. The certificate's axioms are exactly `propext,
  Classical.choice, Quot.sound`. No `@trusted`, no `assume`, no `sorry` anywhere.
* **TypeScript.** `npx tsc --noEmit -p .` reports no errors.
* **The app runs.** `npx vite --port 5181 --strictPort` started in under a second. curl got
  HTTP 200 for the page and for every module (`main.tsx`, `App.tsx`, `OptionsChain.tsx`,
  `StrikeRow.tsx`, `TermRow.tsx`, `OrderTicket.tsx`, `model.ts`, `reducer.ts`, `styles.css`, React
  and `vreact/spec`). The server was then stopped.

After step 22 we also tuned the demo data and one default. The generated quotes had been too
close to their theoretical values, so most cells lit up in the heat map. The data was
regenerated with realistic spreads, and the default threshold went from 2 ticks to 1. The final
log is from the tuned version. Earlier snapshots keep the earlier numbers.

---

## What exactly is proven

`App.certificate` is a Lean theorem: in every run of the application, meaning any sequence of
clicks and other user events, effect runs and timer firings in vreact's model of React 18, every
mounted component instance satisfies its invariant. Lean's kernel checked it, and it depends on
no assumption beyond Lean's standard axioms. In terms of this app, together with the
per-component obligations that the certificate is built from:

**State that can never go wrong**

* The UI state is always well-formed: the heat threshold is 1–5 ticks. Every working order has
  a quantity of 1–500 lots and a positive price. Order ids are distinct and below `nextId`, so a
  new order never reuses one.
* An open ticket always has a positive price. The order ticket's own quantity and price are
  always valid.
* The simulated futures never move more than ±40 ticks, whatever the interleaving of timer
  ticks, re-renders and clicks.
* Each of these survives any new props the parent passes, including expiries disappearing.

**Rendering never fails** (in any reachable state, for any valid data):

* every array index is in bounds (e.g. the ATM row, at both edges of the ladder);
* every called function's precondition holds (`strikeWindow`'s ATM row, `heatOf`'s threshold);
* every division is by a non-zero number (price and volatility formatting);
* every list's keys are distinct (expiry ids, strikes, orders, filter and lot buttons);
* every child's precondition holds (`StrikeRow` gets a valid threshold, `OrderTicket` a
  positive price, the chain valid data).

**Callbacks do what they say**

* A price cell reports exactly the price it shows. `StrikeRow` reports exactly the clicked
  cell's call/put, bid/ask and price. `TermRow` reports the futures price it shows. So a ticket
  opened from a cell carries that cell's contract, side and price.
* `OrderTicket` submits only valid orders.
* Every callback a parent hands to a child keeps the parent's invariant.

**Functional properties of the model** (the `ensures`, each proved for all inputs):

* `atmIndex`: in range. When it reports a row, that strike is a nearest strike to the price (no
  strike is strictly nearer). It reports a row whenever a nearest strike exists.
* `strikeWindow`: in range, contains the ATM row, and contains *exactly* the rows within
  `levels` rows of it.
* `heatOf`: the colour is exactly the documented one for every edge, threshold and missing
  quote.
* `midPrice`: the mid rounded down when two-sided (and then it lies within the spread),
  otherwise the side present, otherwise null.
* Reducer operations: what each one achieves, plus frame conditions (e.g. unlocking one expiry
  keeps the other expiries' holds, the filter, the focus and the threshold).
* `stepFeed`, `moveFutures`: they preserve validity.

**Events are modelled faithfully** (`vreact/docs/SEMANTICS.md` §2): discrete events (clicks)
are checked against the state the user saw. Timers are checked against any state. The App's
click is also checked against React's rebasing onto a pending timer update.

### The trusted base

What a reader has to trust, following `vreact/docs/SEMANTICS.md` §5:

* the **translation** from TypeScript to Lean and the **report** that reads Lean's output;
* the **JavaScript runtime model** (that `findIndex`, `slice`, `%`, template strings … behave as
  modelled) and the **React model** (React 18's batching, update queues, rebasing,
  reconciliation, event priorities);
* Lean's kernel, plus the standard axioms;
* outside the model: `main.tsx`, React itself, the DOM, the browser's anchor navigation (the
  "jump" scroll), and the CSS (the heat colours are a stylesheet, not a proof).

### Not proven here

* That a nearest strike always exists for a non-empty ladder (true, but it needs induction; see
  below). The UI falls back to showing every strike if `atmIndex` ever returned −1.
* That the strikes are ascending. Nothing depends on it except the display order.
* That the numbers end up in the right columns and the right colours on screen. Only the
  callback contracts tie a cell to the price it shows.
* That the ticket resets when another cell is clicked. This is done with a `key`, which is not
  verified.
* Anything about theoretical values, volatilities or the demo data, beyond `validChain`.
* Integer overflow: `int` is unbounded in the model. The values here are far below 2^53.

---

## Where the tool pushed back

Each item below is a true statement the automation could not handle, or a construct VTS
rejected. Each was resolved by restructuring the code. No `assume`, `@trusted` or Lean proof
was added.

1. **`implies` in synth's random tests** (steps 02–03). Synth evaluates contracts as
   JavaScript, so `implies(r >= 0, nearest(ks, ks[r], price))` evaluates `ks[-1].strike` and
   throws. Every candidate then fails ("no candidate passed the tests"), even `-1`, which Lean
   proves. *Fix:* write guards that short-circuit in JavaScript too: `r < 0 || …`.
2. **The bracket ATM search** (step 05). Proving that "first strike at or above the price, or
   the one below" is nearest needs two facts the automation lacks: that `findIndex` returns the
   *first* match, and that an ascending order is transitive. *Fix:* compute the ATM as "the
   first strike that no other strike beats" (`findIndex` over the `@opaque` predicate
   `nearest`). That is O(n²) on ~15 strikes, and its proof is one known fact.
3. **Existence of a nearest strike** (step 06). "A non-empty ladder has a nearest strike" needs
   induction. *Fix:* the postcondition says "an ATM row is found whenever some strike is
   nearest". That excludes the `-1` escape hatch and is provable. The remaining gap is a plain
   mathematical fact, listed above under "not proven".
4. **Synth offers the reducer as a building block** (steps 08–10). While `chainReducer` exists,
   synth proposes `chainReducer(u, …)` inside the operations it calls ("mutually recursive
   declarations are not supported") and stops after three such untestable candidates. *Fix:*
   synthesize the operations first, then write the reducer.
5. **Enum keys** (step 13): `keys must be int or string`. *Fix:* `key={filterLabel(f)}`.
6. **Ternary of `int | null` and a narrowed `int`** (step 13b): `type mismatch: expected int, got
   int | null`. *Fix:* annotate the const (`const center: int | null = …`).

---

## Try it yourself

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain
cd examples/options-chain
npx vreact verify                 # ✔ VERIFIED 129/129, certificate on standard axioms
npx vreact synth src/model.ts     # nothing left to fill: "no hole<T>() in src/model.ts"
npx tsc --noEmit -p .             # clean
npm run dev                       # http://localhost:5173

# then break something and watch the verifier catch it, e.g. in StrikeRow.tsx:
#   onPick={(x) => props.onPick("put", "ask", x)}   on the put *bid* cell  → [callback-contract]
#   hi: Math.min(n, atm + levels)                   in strikeWindow        → [postcondition]
```

Replay the whole walkthrough. Each step's snapshot is copied into a temp project, the same
command is run (without `--write`), and the verdict and per-item statuses are compared with the
saved log:

```bash
bash docs/options-chain/replay.sh           # all steps, about 15 minutes; exits non-zero on any mismatch
bash docs/options-chain/replay.sh 05 16     # just steps 05 and 16
```

---

## The steps and their logs

| step | command | result | snapshot | log |
|---|---|---|---|---|
| 01 model spec | `verify` | ◐ INCOMPLETE, 5 holes | [src](options-chain/steps/01-model-spec/src/) | [log](options-chain/01-model-spec.txt) |
| 02 synth | `synth src/model.ts` | `midPrice = q.bid`: weak spec | [src](options-chain/steps/02-model-synth/src/) | [log](options-chain/02-model-synth.txt) |
| 03 synth, JS-safe guard | `synth src/model.ts` | `atmIndex = 0 - 1`: weak spec | [src](options-chain/steps/03-model-synth-guard/src/) | [log](options-chain/03-model-synth-guard.txt) |
| 04 synth, strong spec | `synth src/model.ts --write` | `quotePrice` written | [src](options-chain/steps/04-model-synth-strong/src/) | [log](options-chain/04-model-synth-strong.txt) |
| 05 hand-written model | `verify` | ✗ ATM edges, window off-by-one | [src](options-chain/steps/05-model-bugs/src/) | [log](options-chain/05-model-bugs.txt) |
| 06 ATM as a search | `verify` | ✗ existence (induction) | [src](options-chain/steps/06-model-search/src/) | [log](options-chain/06-model-search.txt) |
| 07 model verified | `verify` | ✔ 22/22 | [src](options-chain/steps/07-model-verified/src/) | [log](options-chain/07-model-verified.txt) |
| 08 reducer synth | `synth src/reducer.ts` | `cancel = u`, `follow = jump(u, id)` | [src](options-chain/steps/08-reducer-synth/src/) | [log](options-chain/08-reducer-synth.txt) |
| 09 frame conditions | `synth src/reducer.ts --write` | synth stuck on `chainReducer` | [src](options-chain/steps/09-reducer-synth-strong/src/) | [log](options-chain/09-reducer-synth-strong.txt) |
| 10 ops before the reducer | `synth src/reducer.ts --write` | `follow`, `cancel` written | [src](options-chain/steps/10-reducer-synth-ops/src/) | [log](options-chain/10-reducer-synth-ops.txt) |
| 11 hand-written ops | `verify` | ✗ `place` reuses an id | [src](options-chain/steps/11-reducer-bug/src/) | [log](options-chain/11-reducer-bug.txt) |
| 12 reducer verified | `verify` | ✔ 44/44 | [src](options-chain/steps/12-reducer-verified/src/) | [log](options-chain/12-reducer-verified.txt) |
| 13 chain, enum key | `verify` | ✗ VTS: keys must be int or string | [src](options-chain/steps/13-chain-key-rejected/src/) | [log](options-chain/13-chain-key-rejected.txt) |
| 13b chain, ternary | `verify` | ✗ VTS: type mismatch | [src](options-chain/steps/13b-chain-ternary-rejected/src/) | [log](options-chain/13b-chain-ternary-rejected.txt) |
| 14 chain vs stubs | `verify` | ✗ ATM edge in the chain | [src](options-chain/steps/14-chain-atm-edge/src/) | [log](options-chain/14-chain-atm-edge.txt) |
| 15 chain vs stubs, fixed | `verify` | ✔ VERIFIED* 75/75 | [src](options-chain/steps/15-chain-topdown/src/) | [log](options-chain/15-chain-topdown.txt) |
| 16 props-tied invariant | `verify` | ✗ props-stability | [src](options-chain/steps/16-props-stability/src/) | [log](options-chain/16-props-stability.txt) |
| 17 look up and clamp | `verify` | ✔ VERIFIED* 76/76 | [src](options-chain/steps/17-props-clamped/src/) | [log](options-chain/17-props-clamped.txt) |
| 18 StrikeRow | `verify` | ✗ callback-contract | [src](options-chain/steps/18-strikerow-bug/src/) | [log](options-chain/18-strikerow-bug.txt) |
| 19 StrikeRow fixed | `verify` | ✔ VERIFIED* 98/98 | [src](options-chain/steps/19-strikerow/src/) | [log](options-chain/19-strikerow.txt) |
| 20 TermRow, OrderTicket | `verify` | ✗ handler (price → 0) | [src](options-chain/steps/20-children-bug/src/) | [log](options-chain/20-children-bug.txt) |
| 21 all children | `verify` | ✔ VERIFIED 122/122 | [src](options-chain/steps/21-children-verified/src/) | [log](options-chain/21-children-verified.txt) |
| 22 moving market | `verify` | ✗ effect-robust | [src](options-chain/steps/22-app-stale-timer/src/) | [log](options-chain/22-app-stale-timer.txt) |
| 23 final | `verify` | ✔ VERIFIED 129/129 | [src](options-chain/steps/23-final/src/) | [log](options-chain/23-final.txt) |
