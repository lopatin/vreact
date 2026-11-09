# Walkthrough: building a verified options chain

This walkthrough builds `examples/options-chain`, a medium-complexity trading widget, with
vreact from an empty folder to a **fully verified** React app. The result has 6 components,
49 functions (the reducer among them) and 131 proof obligations. Its whole-app certificate
depends only on Lean's three standard axioms. Near the end, we test the specification itself
by breaking the code on purpose, and then list exactly what is and is not proven.

It is written for a developer who knows React and TypeScript but has never used formal
verification. Each new idea is explained the first time it appears. Every tool output below
comes from a real run. The raw logs are in [`options-chain/`](options-chain/), and a full
snapshot of `src/` at each step is in [`options-chain/steps/`](options-chain/steps/).
[`options-chain/replay.sh`](options-chain/replay.sh) re-runs every step and checks that the tool
still says the same thing. The snapshots are for `vreact verify` and the replay: they hold
`src/` only, without the project's configs, and those before step 23 have no `styles.css`
(which `main.tsx` imports). The app you can run is
[`examples/options-chain`](../examples/options-chain/).

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
8. [Step 7: audit the spec with mutants](#step-7-audit-the-spec-with-mutants)
9. [Step 8: final checks](#step-8-final-checks)
10. [What exactly is proven](#what-exactly-is-proven)
11. [Where the tool pushed back](#where-the-tool-pushed-back)
12. [Try it yourself](#try-it-yourself)
13. [The steps and their logs](#the-steps-and-their-logs)

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

`int` comes from `vreact/spec`. For TypeScript and at runtime it is just `number`. The verifier
reads it as a mathematical integer, so integer code may use `+ - *` and comparisons. `/` would
give a `number`; integer division is `idiv(a, b)`, which rounds down.

---

## 1. Setup

From a fresh clone (Node ≥ 22.6, Lean 4 via [elan](https://github.com/leanprover/elan)):

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain   # npm deps + Lean library
cd examples/options-chain
npx vreact verify          # ✔ VERIFIED 131/131
npm run dev                # the same .tsx files, running in React 18
```

The app was created by copying the setup of `examples/cart`: `package.json`, `tsconfig.json`
(`"strict": true`, `"lib": ["ES2023", "DOM"]`), `vite.config.ts`, `index.html`, a `.gitignore`
with `.vreact/`, and `vreact.json`:

```json
{ "src": "src", "exclude": ["main.tsx"], "proofs": "proofs", "out": ".vreact" }
```

`main.tsx` only mounts `<App/>`. It stays outside the verified program. The logs of this
walkthrough were made the way the replay runs a step (see "Try it yourself"): the step's
snapshot in a temp project with the app's configs and a `node_modules` symlink, and the command
run as `node <repo>/vreact/bin/vreact.js …`. `npx vreact …` is the same program.

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

`@opaque` (the tag in the doc comment of `nearest`) tells vreact that proofs elsewhere should
see only the function's name and contract, not its body. For a specification predicate like
`nearest`, that is what we want: it stays one fact instead of being unfolded into a loop over
the ladder.

`requires`, `ensures`, `hole` and the helpers in the contracts come from `vreact/spec`, like
`int`. At runtime the contract statements do nothing (an unfilled `hole()` throws), and the
helpers are ordinary functions that the verifier also understands: `implies(a, b)` is "if `a`
then `b`", `forall(lo, hi, (i) => …)` says the condition holds for every integer `i` with
`lo <= i < hi`, and `distinct(xs, key)` says no two elements of `xs` have the same key.

```
$ vreact verify
translated 1 module(s), 6 proof obligation(s) → .vreact/ ; checking with Lean…
…
Functions
  VERIFIED           validChain
  …
  INCOMPLETE         quotePrice
      ↳ pending: it has a hole() / sorry
  …
  INCOMPLETE         atmIndex
      ↳ an obligation of it was not checked: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first
  …
Obligations by file
  ? src/model.ts                             5/6  (1 not checked)

1 obligation(s) not checked:
  src/model.ts:103:51: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first
pending (hole() / sorry): quotePrice, midPrice, strikeWindow, heatOf

◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)  5/6 obligations proved, 1 unchecked; components: 0/0 verified  (6.1s)
```

A **proof obligation** is one claim that must be true for the program to be correct, such as
"this index is in bounds" or "this function returns what its `ensures` says". `vreact verify`
translates the code to Lean 4 and asks Lean to prove every obligation. A function is
`VERIFIED` when all of its obligations are proved, and `INCOMPLETE` while it still has a hole.

The one obligation that is **not checked** (`?`, "1 unchecked") is the index `ks[r]` in
`atmIndex`'s second `ensures` (line 103, column 51). To show that `r` is in bounds, Lean needs
to know what the function returns, and the body is still a hole. In Lean a hole is a `sorry`,
a placeholder for something missing. An obligation whose goal or proof contains a `sorry`
from elsewhere would prove nothing, so it is neither counted as proved nor as failed; it is
checked again once the hole is filled.

### 1b. Let the synthesizer test the spec ([log](options-chain/02-model-synth.txt))

`vreact synth` enumerates small programs, smallest first. It runs each one as JavaScript on
random inputs against the contracts, and asks Lean to prove the ones that pass.

```
$ vreact synth src/model.ts
…
hole 2/2 in quotePrice: int | null   scope: q, q.bid, q.bidQty, q.ask, q.askQty, side
  candidate passes 196 random tests: q.ask   (2 candidate(s) tested in 0.0s)
  ✔ proved by Lean: quotePrice with q.bid / q.ask
hole in midPrice: int | null   scope: q, q.bid, q.bidQty, q.ask, q.askQty
  candidate passes 400 random tests: q.bid   (1 candidate(s) tested in 0.0s)
  ✔ proved by Lean: q.bid
hole in atmIndex: int   scope: ks, price
  14785 candidates tested in 60.0s, up to size 7; stopped: the 60s time limit was reached at size 7
  no verified solution for hole in atmIndex: no candidate passed the tests
  most common failure (14785×): price: postcondition fails on [[{"strike":1,"call":{"bid":10,"bidQty":1,"ask":null,"askQty":-1},"put":{"bid":10,"bidQty":1,"ask":7,"askQty":0},"callTheo":-1,"putTheo":4,"vol":-10}],-1] ↦ -1
…
```

The test inputs are random. Test counts, candidate counts, timings and counterexamples
differ from run to run, so a re-run will not print these exact numbers. The verdicts and the
fills are the same each time (the replay checks them).

`quotePrice` is filled as expected. The `midPrice` result is a warning: **`return q.bid`
satisfies its contract.** The first contract only said "null when both sides are missing" and
"within the spread", and the bid is within the spread. A verified function is only as good as
its specification, and the synthesizer just showed that ours does not say "mid".

For `atmIndex`, no candidate passed, not even the trivial `-1`. The reason is how synth tests:
it runs the contracts as JavaScript, where `implies(a, b)` is an ordinary function call that
evaluates `b` even when `a` is false. For `r = -1`, `ks[-1].strike` throws. (The failure printed
above is such a case: on a one-strike ladder and the price −1, the candidate `price` returns
−1.) In Lean, `implies` is guarded. We write the same condition with `||`, which short-circuits
in both languages ([log](options-chain/03-model-synth-guard.txt)):

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
  most common failure (10143×): q.bid: postcondition fails on [{"bid":1,"bidQty":2,"ask":-2,"askQty":2}] ↦ 1
…
wrote src/model.ts
```

`q.bid` is now refuted by a concrete input (a bid of 1 and an ask of −2: the mid, rounded down,
is −1, not 1). The rest needs branches, which synth does not build ("write this one by hand").
`--write` keeps the one proved fill.

### 1c. Hand-written code, machine-checked ([log](options-chain/05-model-bugs.txt), [snapshot](options-chain/steps/05-model-bugs/src/model.ts))

The first hand-written `atmIndex` is the usual fast search for a sorted ladder, and the
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
✗ src/model.ts:125:18  [index] index k - 1 is within bounds of ks
    │ `grind` failed
    │ …
    │ k : Int := JS.findIndex ks fun s => JS.le price s.strike
    │ …
    │ h : (JS.findIndex ks fun s => JS.le price s.strike) ≤ 0
    │ h_1 : (JS.findIndex ks fun s => JS.le price s.strike) = -1
    │ …
    │ right : ∀ (x : Strike), x ∈ ks → JS.le price x.strike = false
    │ ⊢ False
✗ src/model.ts:125:38  [index] index k is within bounds of ks
    │ …
    │ h : (JS.findIndex ks fun s => JS.le price s.strike) + 1 ≤ 0
    │ ⊢ False
✗ src/model.ts:139:11  [postcondition] postcondition of strikeWindow: 0 <= r.lo && r.lo <= atm && atm < r.hi && r.hi <= n
    │ …
    │ h_pre_1 h_pre : (0 ≤ atm ∧ atm < n) ∧ levels ≥ 0
    │ h : -1 * atm + min n (atm + levels) ≤ 0
    │ h_1 : ¬n + -1 * atm + -1 * levels ≤ 0
    │ ⊢ False
✗ src/model.ts:140:11  [postcondition] postcondition of strikeWindow: forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, leve…
…
4 obligation(s) not checked:
  src/model.ts:116:11, src/model.ts:119:44, src/model.ts:119:11, src/model.ts:121:11: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first

✗ NOT VERIFIED  16/24 obligations proved, 4 failed, 4 unchecked; components: 0/0 verified  (18.3s)
```

Some vocabulary first. vreact proves each obligation with `vreact_auto`, its automation, whose
main tool is `grind`, an automatic Lean tactic for this kind of goal (equalities, linear
arithmetic, case splits). "`grind` failed" means it ran out of ideas, and the goal it prints is
where it stopped. A failure does not stop the check: vreact admits the failed goal (with
`sorry`) and goes on, so one run reports every failure.

How to read a failure: the lines above `⊢` are what Lean knows at that point (hypotheses), and
`⊢ False` means they were not enough. Often they *are* a counterexample:

* **`[index] k` and `[index] k - 1`: the ATM at the edges, a real bug.** In the `[index] k` goal,
  `h` says `k + 1 ≤ 0`, so `k = -1`: `findIndex` found no strike at or above the price, which is
  what happens when the futures trade above the top strike. Then `ks[k]` is read out of bounds.
  In the `[index] k - 1` goal, `h` says `k ≤ 0`. That includes `k = 0`: the price is at or below
  the bottom strike, there is no strike below it, and `ks[k - 1]` is out of bounds. The case
  printed (`h_1`, `right`) is `k = -1` again. In JavaScript these reads give `undefined`, then a
  `TypeError` in render. After a large move of the underlying, this is a realistic situation.
* **`strikeWindow`: an off-by-one, a real bug.** `h` and `h_1` together say
  `min(n, atm + levels) ≤ atm` while `atm + levels < n`, so `levels = 0`. With `levels = 0`, the
  window `[atm, atm)` is empty and the ATM row disappears. In general the last row
  `atm + levels` is missing: the filter "3" showed 3 rows below the ATM row but only 2 above.
  The fix is `hi: Math.min(n, atm + levels + 1)`.
* **`atmIndex`'s postconditions: not checked, and false anyway.** The three `ensures` of
  `atmIndex` (lines 116, 119 and 121, and the index `ks[r]` inside the second one) are about
  the value the function returns, and that value is computed from `ks[k - 1]` and `ks[k]`,
  whose index obligations failed. A proof through an admitted failure would rest on a false
  statement and prove nothing, so vreact does not count it: these obligations are "not
  checked" until the failures they depend on are fixed. Here, fixing the reads would not be
  enough, because the statements are false for this code, so no prover could prove them. Two
  of them are the edge bug again: above the top strike, `k = -1`, and the function returns
  `k - 1` or `k`, both negative (`-2` is not even in the range `-1 <= r`), although the ladder
  is not empty. The third, "the result is a nearest strike", is false even away from the
  edges. The search silently assumes an ascending ladder, and no contract says so:
  `validChain` asks only for distinct strikes. Take the ladder `[10, 100, 50, 12]` (in ticks)
  and the price 60. The first strike at or above 60 is 100, the one before it is 10, and 100 is
  nearer, so the search returns the strike 100, 40 ticks away, while 50 is only 10 ticks away.
  Lesson: when an obligation is not proved, look for a counterexample before blaming the
  automation.

### 1d. Make the code easy to prove ([log](options-chain/06-model-search.txt), [log](options-chain/07-model-verified.txt))

One way out is to state the assumption: require an ascending ladder in `validChain` and in
`atmIndex`, and prove the bracket search under it. We did not try that. Instead we write an
`atmIndex` that is correct for a ladder in any order, and whose correctness is immediate:
return the first strike that no other strike beats.

```ts
// the first strike that no other strike beats (O(n²) on a ladder of ~15 strikes)
return ks.findIndex((s) => nearest(ks, s, price));
```

There are no indices, so there are no edges, and no assumption about the order of the ladder.
"The strike at the returned index satisfies the predicate" is a known fact about `findIndex`,
and it is exactly the postcondition. This is why
`nearest` is `@opaque`: the predicate in the code and the predicate in the contract are the same
atom. One obligation still fails:

```
✗ src/model.ts:121:11  [postcondition] postcondition of atmIndex: implies(ks.length > 0, r >= 0)
    │ `grind` failed
    │ …
    │ h₂₁ : ↑ks.length > 0
    │ …
    │ h : (JS.findIndex ks fun s => nearest ks s price) + 1 ≤ 0
    │ ⊢ False

✗ NOT VERIFIED  21/22 obligations proved, 1 failed; components: 0/0 verified  (7.2s)
```

The goal is the case of a non-empty ladder (`h₂₁`) in which `findIndex` found no nearest strike
and returned −1 (`h`). That case cannot happen: "a non-empty ladder has a nearest strike" is
true. But proving it is an induction over the list (a minimum exists), and the automation does
not do induction. We state what is provable and still rules out the escape hatch:

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

✔ VERIFIED  22/22 obligations proved; components: 0/0 verified  (8.5s)
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

### 2a. Synthesis finds three weak specs ([log](options-chain/08-reducer-synth.txt))

```
$ vreact synth src/reducer.ts
hole in setCollapsed: ChainUi   …
  ✔ proved by Lean: { ...u, collapsed: ids }
hole in setFilter: ChainUi   …
  ✔ proved by Lean: { ...u, filter: f }
hole in holdAt: ChainUi   …
  candidate passes 400 random tests: { ...u, held: [{ expiry: id, price: price }] }   (12658 candidate(s) tested in 44.5s)
  ✔ proved by Lean: { ...u, held: [{ expiry: id, price: price }] }
hole in follow: ChainUi   …
  candidate passes 400 random tests: jump(u, id)   (17 candidate(s) tested in 0.1s)
  ✔ proved by Lean: jump(u, id)
hole in place: ChainUi   …
  19699 candidates tested in 60.0s, up to size 6; stopped: the 60s time limit was reached at size 6
  no verified solution for hole in place: no candidate passed the tests
…
hole in cancel: ChainUi   …
  candidate passes 400 random tests: u   (1 candidate(s) tested in 0.0s)
  ✔ proved by Lean: u
```

* `cancel` (contract: keeps the invariant) is satisfied by **doing nothing**.
* `follow` (contract: afterwards the expiry follows the futures price) is satisfied by
  **`jump(u, id)`**, which also expands the expiry and moves the focus. The contract never said
  that everything else stays the same. That missing part is called a **frame condition**.
* `holdAt` (contract: afterwards the expiry is held at `price`) is satisfied by
  **`{ ...u, held: [{ expiry: id, price: price }] }`**, which holds this expiry and silently
  drops the holds of every other expiry. The same frame condition is missing.

`place` needs a guard (an invalid quantity or price adds nothing), and synth does not build
`if`s: it is written by hand in 2c.

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

### 2b. Synthesis with the frame conditions ([log](options-chain/09-reducer-synth-strong.txt), [log](options-chain/10-reducer-synth-ops.txt))

With the stronger specs, synth fills `follow` and `cancel`:

```
$ vreact synth src/reducer.ts --write
…
hole in follow: ChainUi   …
  candidate passes 400 random tests: { ...u, held: u.held.filter((x) => x.expiry !== id) }   (9690 candidate(s) tested in 30.0s)
  ✔ proved by Lean: { ...u, held: u.held.filter((x) => x.expiry !== id) }
…
hole in cancel: ChainUi   …
  candidate passes 400 random tests: { ...u, orders: u.orders.filter((x) => x.id !== id) }   (12887 candidate(s) tested in 39.4s)
  ✔ proved by Lean: { ...u, orders: u.orders.filter((x) => x.id !== id) }
wrote src/reducer.ts
```

Both are the intended programs. With the frame conditions in place, synth's answer is the right
one. `holdAt` and `place` are not found within the 60 s that synth spends on each hole.

Step 10 runs the same search with `chainReducer` removed
([snapshot](options-chain/steps/10-reducer-synth-ops/src/reducer.ts)) and finds the same two
programs. That step was a workaround for an earlier synth, which offered every total function
of the module as a building block, including `chainReducer`, which calls the very operations
being synthesized. Those candidates could not be translated ("mutually recursive declarations
are not supported"), and the search gave up on every hole. Synth now leaves out any function
that calls the one being filled (VTS has no recursion, so such a fill could never translate).
Synthesizing the operations before writing the reducer that calls them is still the natural
order.

### 2c. The rest by hand ([log](options-chain/11-reducer-bug.txt), [log](options-chain/12-reducer-verified.txt))

`holdAt` puts the new hold first (because `heldPrice` reads the first hold of an expiry).
`place` validates and appends. Besides keeping the invariant, its contract promises that a
valid order with the next id, the quantity and the price is added:

```ts
ensures((r: ChainUi) => implies(validQty(qty) && price > 0, r.orders.some((o) => o.id === u.nextId && o.qty === qty && o.price === price)));
if (!validQty(qty) || price <= 0) return u;
const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike,
                   buy: t.side === "ask", qty: qty, price: price };
return { ...u, orders: [...u.orders, o] };
```

(This contract says nothing about the order's contract, strike or direction, and has no frame
condition. Step 7 shows what that lets through.)

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
✗ NOT VERIFIED  43/44 obligations proved, 1 failed; components: 0/0 verified  (12.0s)
```

The counterexample is the new order `x` itself, whose id is `u.nextId`: `nextId` was never
advanced, so the next order would reuse the id. The fix is `nextId: u.nextId + 1`:

```
✔ VERIFIED  44/44 obligations proved; components: 0/0 verified  (9.0s)
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
callback prop. Here: whenever `StrikeRow` calls `onPick(right, side, price)`, `price` is the
current quote of that strike's call or put (`right`) on that side. The parent may rely on it,
and the child is checked against it. Note what it does not say: *which* cell was clicked. The
stub's comment promises more than its contract; step 7 comes back to this. `TermRow` promises
the same for the futures prices, and `OrderTicket` promises to submit only valid orders
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

A quick rejection came first. VTS does not unify a ternary whose branches are `int | null` and a
narrowed `int` ([log](options-chain/13b-chain-ternary-rejected.txt)): `✗ VTS
src/OptionsChain.tsx:98:42: type mismatch: expected int, got int | null`. The annotation `const
center: int | null` above fixes that. Step 13's snapshot, one draft earlier, also used the
filter value itself as the key of its button: `key={f}`, where `f` is an *enum* (VTS's name for
a string-literal union type such as `StrikeFilter = "s3" | "s7" | "s11" | "s99" | "all"`). When
this walkthrough was first written, VTS rejected that (`keys must be int or string`), and the
filter buttons got `key={filterLabel(f)}`. vreact now accepts an enum key (the key is its
string), so step 13 now stops at the same ternary as step 13b
([log](options-chain/13-chain-key-rejected.txt)). `key={filterLabel(f)}` stays; either key
works. Then the first real result ([log](options-chain/14-chain-atm-edge.txt)):

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
✗ src/OptionsChain.tsx:101:67  [precondition] precondition of strikeWindow(n, atm, levels)
    │ …

1 obligation(s) not checked:
  src/OptionsChain.tsx:107:20: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first
…
✗ NOT VERIFIED  72/75 obligations proved, 2 failed, 1 unchecked; components: 0/5 verified  (66.5s)
```

The short report cuts the goal off before the interesting part. `vreact verify --full` prints
it whole ([log](options-chain/14-chain-atm-edge-full.txt)). Its key lines, from the first
goal:

```
$ vreact verify --full
…
    │ atm : Int :=
    │   match h₈ : center with
    │   | some center_1 => model.atmIndex e.strikes center_1
    │   | none => -1
…
    │ heq :
…
    │     some held_1
…
    │ h : (JS.findIndex e.strikes fun s => model.nearest e.strikes s held_1) + 1 ≤ 0
…
    │ h₂₂ h_7 : σ.ui.filter = model.StrikeFilter.s3
…
    │ ⊢ False
```

Read together: `heq` (elided here, it spells out `held` and `live`) ends in `= some held_1`, so
the center is some price `held_1`; `h` says `atmIndex` returned −1 (the `findIndex` result plus
1 is at most 0); and the filter is "3". `atmIndex`'s contract allows −1 when no strike is
nearest, which is the case for an empty ladder. The code shows a second way to get −1:
`center` is `null` when there is no price at all (no bid, no ask, nothing held). Either way
`strikeWindow`'s precondition `0 <= atm` fails. This is the **ATM at the edge, one level up**.

Why is the same call reported twice? The translation evaluates the `map` callback over the
expiries twice: once to compute each `<tbody>`'s key, and once to build its rows. The second
goal is the same case, with one more fact (`hmem₁₃ : e ∈ props.expiries`). For the same
reason, the obligation that the `<tbody>` keys are distinct (line 107) is not checked: the keys
are computed through the failed call, so its goal contains the `sorry` that stands for it.

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

✔ VERIFIED modulo @trusted declarations  75/75 obligations proved; components: 0/5 verified  (21.1s)
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
✗ NOT VERIFIED  77/78 obligations proved, 1 failed; components: 0/5 verified  (21.8s)
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
✔ VERIFIED modulo @trusted declarations  76/76 obligations proved; components: 0/5 verified  (19.1s)
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
…
  INCOMPLETE         StrikeRow              src/StrikeRow.tsx:37
      ↳ an obligation of it failed
  TRUSTED            OrderTicket            src/OrderTicket.tsx:16
  INCOMPLETE         OptionsChain           src/OptionsChain.tsx:32
      ↳ it uses StrikeRow (src/StrikeRow.tsx), which is not verified: an obligation of it failed
…
✗ src/StrikeRow.tsx:55:110  [callback-contract] callback contract of onPick("put", "ask", x)
    │ `grind` failed
    │ …
    │ hpre_1 : props.heat ≥ 1
    │ …
✗ NOT VERIFIED  97/98 obligations proved, 1 failed; components: 1/6 verified  (22.4s)
```

A **callback-contract** obligation says that a call of a callback prop satisfies its
`callbackRequires`. Line 55 is the put **bid** cell, which reports `"ask"`. Clicking a put's bid
would have opened a *buy* ticket at the *bid* price. The contract catches this because the
report contradicts itself: the bid's price under the name "ask". (A cell that reported another
cell's name together with that cell's price would not contradict itself; step 7 comes back to
that.) The chain and the App are `INCOMPLETE` too, although all their own obligations are
proved: they use `StrikeRow`, so they rest on the `sorry` that admits its failed obligation (the
certificate lists it among its axioms as `sorryAx`). After the fix (`"bid"`), `StrikeRow` and
`PriceCell` are `VERIFIED`, and the chain and the App are back to `VERIFIED*`: `✔ VERIFIED
modulo @trusted declarations  98/98 obligations proved; components: 2/6 verified`.

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
…
✗ src/OrderTicket.tsx:46:17  [handler] onClick handler on <button> preserves the invariant of OrderTicket
    │ …
    │ hinv : (1 ≤ σ.qty ∧ σ.qty ≤ 500) ∧ σ.price > 0
    │ h : σ.price + -1 ≤ 0
    │   …

✗ NOT VERIFIED  121/122 obligations proved, 1 failed; components: 3/6 verified  (22.8s)
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

✔ VERIFIED  122/122 obligations proved; components: 6/6 verified  (23.2s)
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
…
✗ src/App.tsx:106:3  [effect-robust] timer callbacks of the effect preserve the invariant of App from any state
    │ `grind` failed
    │ …
    │ hinv : (-40 ≤ σ.offset ∧ σ.offset ≤ 40) ∧ 0 ≤ σ.seed ∧ σ.seed < 65537
    │ …

✗ NOT VERIFIED  127/128 obligations proved, 1 failed; components: 5/6 verified  (46.5s)

$ vreact verify --full     # the same failure, complete goal (excerpt, lines 84-142 of the log)
    │ h :
    │   t = fun x =>
    │     if σ.paused = true then { }
    │     else
    │       if
    │           -40 ≤
    │             σ.offset +
    │               ((if
…
    │               40 then
    │           {
    │             updates :=
    │               [fun τ =>
    │                 { offset := τ.offset,
…
    │                 fun τ =>
    │                 {
    │                   offset :=
    │                     τ.offset +
    │                       ((if
…
    │                         2),
    │                   seed := τ.seed, paused := τ.paused }] }
```

`t` is the timer callback. Its first branch is the effect's `if (paused) return;`, and the long
elided expressions are `move`, computed from `σ.seed`. The guard compares `σ.offset + move` with
−40 and 40, but the second update sets `offset := τ.offset + move`. The timer callback is a
**stale closure**: its guard reads `σ.offset` from the render that created the timer, but its
update `o => o + move` is applied to `τ`, the state React holds when it processes the update.
vreact's model (see `vreact/docs/SEMANTICS.md` §2.2) treats effects and timers as running later,
against any state that satisfies the invariant. So it asks for an **effect-robust** update: one
that keeps the invariant from *every* valid `τ`, not just from the snapshot. With `τ.offset =
40` and `move = +2`, this one does not.

The fix the skill recommends: put the related state in one record, and make the timer apply one
total function to whatever state it finds ([log](options-chain/23-app-feed.txt)):

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

✔ VERIFIED  129/129 obligations proved; components: 6/6 verified  (21.9s)
```

`moveFutures(EXPIRIES, offset)` maps over the constant, and its `ensures` (validity is preserved)
gives the chain its precondition on every tick.

After step 22 we also tuned the demo data and one default. The generated quotes had been too
close to their theoretical values, so most cells lit up in the heat map. The data was
regenerated with realistic spreads, and the default threshold went from 2 ticks to 1. Steps 23
to 26 use the tuned version. Earlier snapshots keep the earlier numbers.

---

## Step 7: audit the spec with mutants

Everything verifies. But step 2 showed that a verified function is only as good as its
contract, and the same holds for the whole app. A cheap way to probe a spec is to break the
code on purpose and see whether the verifier notices. A change that still verifies (a
*surviving mutant*) shows something the spec does not say.

### 7a. Three mutants survive ([log](options-chain/24-mutants.txt), [snapshot](options-chain/steps/24-mutants/src/))

Three one-line changes to the app as it stands after step 6 (snapshot 23), each a plausible bug
in a trading widget:

```tsx
// StrikeRow.tsx, the call-bid cell: report the put's ask instead
onPick={(x) => { if (s.put.ask !== null) props.onPick("put", "ask", s.put.ask); }}
// TermRow.tsx, the futures-bid cell: report the futures ask instead
onPick={(x) => { if (f.ask !== null) props.onPick("ask", f.ask); }}
// reducer.ts, place: every order goes in the wrong direction
const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "bid", qty: qty, price: price };
```

```
$ vreact verify
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
…
✔ VERIFIED  129/129 obligations proved; components: 6/6 verified  (23.4s)
```

All three survive. They are of two kinds.

**The cell mutants are wiring.** `StrikeRow`'s contract is about the arguments of `onPick`:
the reported price is the current quote of the reported leg and side. The mutant reports
(put, ask, the put's ask). That is a correct report, but of another cell. The `TermRow` mutant
likewise reports the futures ask correctly, from the bid cell. No contract on the arguments
can tell which button was clicked: that is a matter of wiring, like the order of the columns.
What the contracts do rule out is a report that contradicts itself, such as the step-18 bug,
where a put's bid price was reported as an ask. Moving `right` and `side` into `PriceCell`'s
props would not change this: the row could still wrap the cell's callback in a closure that
reports something else. So "the report comes from the clicked cell" goes on the "not proven"
list below, and the code keeps the wiring easy to check by eye: one line per cell, with the
price and the report next to each other.

**The `place` mutant is a weak spec.** `place`'s contract (step 2c) promises only an order with
the next id, the quantity and the price. The expiry, the contract, the strike and the
direction were left open, so an app that sells when the ticket says "Buy" still verifies.
This is the lesson of step 2 again, and here it matters most: the direction of an order. The
fix is to say what the order is, and that nothing else changes
([snapshot](options-chain/steps/25-mutants-place-spec/src/reducer.ts)):

```ts
/**
 * `o` is the order a ticket asks for, with id `id`: the ticket's contract, the direction its
 * side implies (clicking an ask buys, clicking a bid sells), the quantity and the price.
 */
export function orderFor(o: Order, id: int, t: Ticket, qty: int, price: int): boolean {
  return (
    o.id === id &&
    o.expiry === t.expiry &&
    o.leg === t.leg &&
    o.strike === t.strike &&
    o.buy === (t.side === "ask") &&
    o.qty === qty &&
    o.price === price
  );
}
…
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  // a valid order is added exactly as the ticket says, under the next id ...
  ensures((r: ChainUi) => implies(validQty(qty) && price > 0, r.orders.some((o) => orderFor(o, u.nextId, t, qty, price))));
  // ... and nothing else changes: one order more (none for an invalid one), the others kept
  ensures((r: ChainUi) => r.orders.length === (validQty(qty) && price > 0 ? u.orders.length + 1 : u.orders.length));
  ensures((r: ChainUi) => keepsOrders(u, r) && keepsAllHolds(u, r) && sameView(u, r));
```

`keepsOrders` says that every working order is still there with the same fields, and
`keepsAllHolds` that every hold is kept. With the three mutants still in the code
([log](options-chain/25-mutants-place-spec.txt)):

```
$ vreact verify
…
  VERIFIED           OptionsChain           src/OptionsChain.tsx:32
  VERIFIED           App                    src/App.tsx:115
…
  INCOMPLETE         place
      ↳ an obligation of it failed
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             22/22
  ✗ src/reducer.ts                           23/24
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     27/27
  ✓ src/App.tsx                              12/12

Failed obligations
✗ src/reducer.ts:175:11  [postcondition] postcondition of place: implies(validQty(qty) && price > 0, r.orders.some((o) => orderFor(o, …
    │ `grind` failed
    │ …
    │ h_2 :
    │   ∀ (a : model.Order),
    │     ¬a ∈ u.orders ∧
    │         ¬a =
    │             { id := u.nextId, expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.bid,
    │               qty := qty, price := price } ∨
    │       ¬a.id = u.nextId ∨
    │         ¬a.expiry = t.expiry ∨
    │           ¬a.leg = t.leg ∨ ¬a.strike = t.strike ∨ ¬a.buy = JS.eq t.side model.Side.ask ∨ ¬a.qty = qty ∨ ¬a.price = price
    │ ⊢ False

✗ NOT VERIFIED  130/131 obligations proved, 1 failed; components: 6/6 verified  (22.0s)
```

`h_2` says that no order in the result fits `orderFor`, and why: the new order has
`buy := JS.eq t.side model.Side.bid`, where the contract asks for `Side.ask`. The two other new
postconditions of `place` (one order more, the rest kept) are proved. `StrikeRow.tsx` and
`TermRow.tsx` are still ✓ with their mutants, as expected.

The verdict is `NOT VERIFIED`, but the chain, the App and the certificate are `VERIFIED`, on the
three standard axioms. That is not a contradiction. The certificate is about invariants, and all
its proofs need from `place` is its first postcondition (the invariant is kept), which is
proved. The failing postcondition, *which* order is added, is a functional contract that no
invariant proof uses, so the failure does not reach them (no `sorryAx` among the axioms). It is
a failed obligation all the same: `place` is `INCOMPLETE`, and the app is not verified until it
is fixed.

### 7b. The final app ([log](options-chain/26-final.txt), [snapshot](options-chain/steps/26-final/src/))

The final app removes the mutants and keeps the stronger `place` contract. Three small edits
come along: `StrikeRow`'s doc comment now says what its contract checks, a comment in
`model.ts` says that no proof relies on the order of the ladder, and the unused `hole` imports
are gone.

```
$ vreact verify
translated 7 module(s), 131 proof obligation(s) → .vreact/ ; checking with Lean…

Components
  VERIFIED           PriceCell              src/StrikeRow.tsx:12
  VERIFIED           StrikeRow              src/StrikeRow.tsx:39
  VERIFIED           TermRow                src/TermRow.tsx:19
  VERIFIED           OrderTicket            src/OrderTicket.tsx:19
  VERIFIED           OptionsChain           src/OptionsChain.tsx:32
  VERIFIED           App                    src/App.tsx:115
Functions
  VERIFIED           validChain
  …
  VERIFIED           keepsAllHolds
  VERIFIED           keepsOrders
  VERIFIED           orderFor
  …
  VERIFIED           place
  …
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           24/24
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     27/27
  ✓ src/App.tsx                              12/12

✔ VERIFIED  131/131 obligations proved; components: 6/6 verified  (21.9s)
```

---

## Step 8: final checks

* **Verification.** `✔ VERIFIED 131/131`. The certificate's axioms are exactly `propext,
  Classical.choice, Quot.sound`. No `@trusted`, no `assume`, no `sorry` and no `hole` anywhere.
  `vreact synth src/model.ts` and `vreact synth src/reducer.ts` both report
  `no hole<T>() in …`.
* **TypeScript.** `npx tsc --noEmit -p .` reports no errors.
* **The app runs.** `npx vite --port 5181 --strictPort` was ready in 107 ms. curl got HTTP 200
  for the page and for every module (`main.tsx`, `App.tsx`, `OptionsChain.tsx`, `StrikeRow.tsx`,
  `TermRow.tsx`, `OrderTicket.tsx`, `model.ts`, `reducer.ts`, `styles.css`). In a browser,
  clicking the 2.95 call bid of DIX DEC 26 102.00 opened "Sell DIX DEC 26 102.00 C" at 2.95
  with the "Marketable" warning, and Submit listed "Sell 1 DIX DEC 26 102.00 C @ 2.95" under
  working orders. The console showed no errors. The server was then stopped.

---

## What exactly is proven

`App.certificate` is a Lean theorem: in every run of the application, meaning any sequence of
clicks and other user events, effect runs and timer firings in vreact's model of React 18, every
mounted component instance satisfies its invariant. Lean's kernel checked it, and it depends on
no assumption beyond Lean's standard axioms. In terms of this app, together with the
per-component obligations that the certificate is built from:

**State that can never go wrong**

* The UI state is always well-formed: the heat threshold is 1–5 ticks. Every working order has
  a quantity of 1–500 lots and a positive price. The ids of the working orders are distinct and
  below `nextId`, so a new order (which gets `nextId`) never collides with a working order's
  id.
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

**What the callbacks report**

* A price cell's button reports exactly the price it displays (`PriceCell`).
* Every report from `StrikeRow` is consistent: the price is the current quote of the leg (call
  or put) and the side (bid or ask) that it names. The same holds for `TermRow` and the futures
  market. This rules out forwarding a cell's price under the wrong side or leg, the bug of
  step 18. It does *not* tie a report to the cell that was clicked: step 7 shows a call-bid
  cell that reports the put's ask, and it verifies. The chain then builds the ticket from the
  report and the row's strike; that step is plain code, and no contract says more about the
  ticket than that its price is positive.
* `OrderTicket` submits only valid orders.
* Every callback a parent hands to a child keeps the parent's invariant.

**Functional properties of the model** (the `ensures`, each proved for all inputs):

* `atmIndex`: in range. When it reports a row, that strike is a nearest strike to the price (no
  strike is strictly nearer), whatever the order of the ladder. It reports a row whenever a
  nearest strike exists.
* `strikeWindow`: in range, contains the ATM row, and contains *exactly* the rows within
  `levels` rows of it.
* `heatOf`: the colour is exactly the documented one for every edge, threshold and missing
  quote.
* `midPrice`: the mid rounded down when two-sided, otherwise the side present, otherwise null.
  When the market is two-sided and not crossed (bid ≤ ask), the result lies within the spread.
* `place` adds exactly the order the ticket asks for (the next id, the ticket's expiry,
  contract and strike, buy for an ask and sell for a bid, the quantity and the price), and only
  that one. It keeps every other working order, every hold and the view (collapsed expiries,
  filter, focus, threshold). An invalid quantity or price adds nothing.
* `holdAt` and `follow` set or clear one expiry's hold, and keep the other expiries' holds and
  the view. `cancel` removes the order and keeps the others (by id).
* `toggle`, `setCollapsed`, `setFilter`, `jump` and `setHeat` state what they change, but have
  no frame conditions: their contracts do not say that the rest of the state stays the same.
* `stepFeed`, `moveFutures`: they preserve validity.

**Events, as modelled in `vreact/docs/SEMANTICS.md` §2**: discrete events (clicks) are checked
against the state the user saw. Timers are checked against any state. The App's click is also
checked against React's rebasing onto a pending timer update. That this model matches React 18
is part of the trusted base below.

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

* That a click reports the cell that was clicked. The contracts check that every report is
  consistent, not where it comes from; a cell whose handler reports another cell's leg, side
  and price verifies (step 7). Likewise, that the numbers end up in the right columns and
  colours on screen, and that texts such as the ticket's "Buy"/"Sell" title match the data:
  rendering is proved not to fail, but its content is not specified.
* That the frame of `toggle`, `setCollapsed`, `setFilter`, `jump` and `setHeat` is kept (see
  above).
* That `nextId` only grows. Nothing proves that the id of a cancelled order is never given to
  a new one; only collisions with working orders are excluded.
* That a nearest strike always exists for a non-empty ladder (true, but it needs induction; see
  below). The UI falls back to showing every strike if `atmIndex` ever returned −1.
* That the strikes are ascending. Nothing depends on it except the display order.
* That the ticket resets when another cell is clicked. This is done with a `key`, which is not
  verified.
* Anything about theoretical values, volatilities or the demo data, beyond `validChain`.
* Integer overflow: `int` is unbounded in the model. The values here are far below 2^53.

---

## Where the tool pushed back

Each item below is a limit of the tool (a quirk of synth, or a true statement the automation
could not prove) or a construct VTS rejected. Each was resolved by restructuring the code. No
`assume`, `@trusted` or Lean proof was added.

1. **`implies` in synth's random tests** (steps 02–03). Synth evaluates contracts as
   JavaScript, so `implies(r >= 0, nearest(ks, ks[r], price))` evaluates `ks[-1].strike` and
   throws. Every candidate then fails ("no candidate passed the tests"), even `-1`, which Lean
   proves. *Fix:* write guards that short-circuit in JavaScript too: `r < 0 || …`.
2. **Existence of a nearest strike** (step 06). "A non-empty ladder has a nearest strike" needs
   induction. *Fix:* the postcondition says "an ATM row is found whenever some strike is
   nearest". That excludes the `-1` escape hatch and is provable. The remaining gap is a plain
   mathematical fact, listed above under "not proven".
3. **Ternary of `int | null` and a narrowed `int`** (steps 13 and 13b): `type mismatch:
   expected int, got int | null`. *Fix:* annotate the const (`const center: int | null = …`).

Two more items were on this list when this walkthrough was first written, and the current
vreact no longer pushes back on either: synth offered `chainReducer` as a building block for
the very operations it calls, and gave up (steps 08–10, see 2b); and VTS rejected enum keys
(step 13, see step 3).

Not on this list: the bracket ATM search of step 05. Its postconditions were not proved (they
were not checked, behind its failed index reads), and they are false: the search assumes an
ascending ladder that no contract promises, so there the verifier was right. Nor are the
surviving mutants of step 7: they are gaps in the spec, not in the tool.

---

## Try it yourself

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain
cd examples/options-chain
npx vreact verify                 # ✔ VERIFIED 131/131, certificate on standard axioms
npx vreact synth src/model.ts     # nothing left to fill: "no hole<T>() in src/model.ts"
npx tsc --noEmit -p .             # clean
npm run dev                       # http://localhost:5173

# then break something and watch the verifier catch it, e.g.:
#   onPick={(x) => props.onPick("put", "ask", x)}   on StrikeRow's put *bid* cell  → [callback-contract]
#   hi: Math.min(n, atm + levels)                   in strikeWindow                → [postcondition]
#   buy: t.side === "bid"                           in place                       → [postcondition]
# and look for mutants that survive: each one is something the spec does not say.
```

Replay the whole walkthrough. Each step's snapshot is copied into a temp project, the same
command is run (without `--write`), and the verdict and per-item statuses are compared with the
saved log:

```bash
bash docs/options-chain/replay.sh           # all steps (~42 minutes; steps 01-26: ~20); non-zero on any mismatch
bash docs/options-chain/replay.sh 05 16     # just steps 05 and 16
bash docs/options-chain/replay.sh --stable docs/options-chain/26-final.txt   # the lines it compares
```

The synth steps run against the clock: each hole has a 60 s budget. In our runs, step 08 found
`holdAt` after 30 to 45 s, and steps 09 and 10 found `cancel` after 35 to 40 s, depending on
the machine's load. On a much slower or busier machine such a fill may not be found in time, and
the replay then reports a mismatch for that step. The budget is wall-clock time, so keep the
machine awake while the replay runs (on macOS: `caffeinate -i bash docs/options-chain/replay.sh`).

---

## The steps and their logs

| step | command | result | snapshot | log |
|---|---|---|---|---|
| 01 model spec | `verify` | ◐ INCOMPLETE, 6 holes in 5 functions | [src](options-chain/steps/01-model-spec/src/) | [log](options-chain/01-model-spec.txt) |
| 02 synth | `synth src/model.ts` | `midPrice = q.bid`: weak spec | [src](options-chain/steps/02-model-synth/src/) | [log](options-chain/02-model-synth.txt) |
| 03 synth, JS-safe guard | `synth src/model.ts` | `atmIndex = 0 - 1`: weak spec | [src](options-chain/steps/03-model-synth-guard/src/) | [log](options-chain/03-model-synth-guard.txt) |
| 04 synth, strong spec | `synth src/model.ts --write` | `quotePrice` written | [src](options-chain/steps/04-model-synth-strong/src/) | [log](options-chain/04-model-synth-strong.txt) |
| 05 hand-written model | `verify` | ✗ ATM edges, window off-by-one | [src](options-chain/steps/05-model-bugs/src/) | [log](options-chain/05-model-bugs.txt) |
| 06 ATM as a search | `verify` | ✗ existence (induction) | [src](options-chain/steps/06-model-search/src/) | [log](options-chain/06-model-search.txt) |
| 07 model verified | `verify` | ✔ 22/22 | [src](options-chain/steps/07-model-verified/src/) | [log](options-chain/07-model-verified.txt) |
| 08 reducer synth | `synth src/reducer.ts` | `cancel = u`, `follow = jump(u, id)`, `holdAt` drops the other holds | [src](options-chain/steps/08-reducer-synth/src/) | [log](options-chain/08-reducer-synth.txt) |
| 09 frame conditions | `synth src/reducer.ts --write` | `follow`, `cancel` written | [src](options-chain/steps/09-reducer-synth-strong/src/) | [log](options-chain/09-reducer-synth-strong.txt) |
| 10 ops before the reducer | `synth src/reducer.ts --write` | the same, without `chainReducer` | [src](options-chain/steps/10-reducer-synth-ops/src/) | [log](options-chain/10-reducer-synth-ops.txt) |
| 11 hand-written ops | `verify` | ✗ `place` reuses an id | [src](options-chain/steps/11-reducer-bug/src/) | [log](options-chain/11-reducer-bug.txt) |
| 12 reducer verified | `verify` | ✔ 44/44 | [src](options-chain/steps/12-reducer-verified/src/) | [log](options-chain/12-reducer-verified.txt) |
| 13 chain, enum key | `verify` | ✗ VTS: type mismatch (the enum key is now accepted) | [src](options-chain/steps/13-chain-key-rejected/src/) | [log](options-chain/13-chain-key-rejected.txt) |
| 13b chain, ternary | `verify` | ✗ VTS: type mismatch | [src](options-chain/steps/13b-chain-ternary-rejected/src/) | [log](options-chain/13b-chain-ternary-rejected.txt) |
| 14 chain vs stubs | `verify` (and `verify --full`) | ✗ ATM edge in the chain | [src](options-chain/steps/14-chain-atm-edge/src/) | [log](options-chain/14-chain-atm-edge.txt), [full](options-chain/14-chain-atm-edge-full.txt) |
| 15 chain vs stubs, fixed | `verify` | ✔ VERIFIED* 75/75 | [src](options-chain/steps/15-chain-topdown/src/) | [log](options-chain/15-chain-topdown.txt) |
| 16 props-tied invariant | `verify` | ✗ props-stability | [src](options-chain/steps/16-props-stability/src/) | [log](options-chain/16-props-stability.txt) |
| 17 look up and clamp | `verify` | ✔ VERIFIED* 76/76 | [src](options-chain/steps/17-props-clamped/src/) | [log](options-chain/17-props-clamped.txt) |
| 18 StrikeRow | `verify` | ✗ callback-contract | [src](options-chain/steps/18-strikerow-bug/src/) | [log](options-chain/18-strikerow-bug.txt) |
| 19 StrikeRow fixed | `verify` | ✔ VERIFIED* 98/98 | [src](options-chain/steps/19-strikerow/src/) | [log](options-chain/19-strikerow.txt) |
| 20 TermRow, OrderTicket | `verify` | ✗ handler (price → 0) | [src](options-chain/steps/20-children-bug/src/) | [log](options-chain/20-children-bug.txt) |
| 21 all children | `verify` | ✔ VERIFIED 122/122 | [src](options-chain/steps/21-children-verified/src/) | [log](options-chain/21-children-verified.txt) |
| 22 moving market | `verify` (and `verify --full`) | ✗ effect-robust | [src](options-chain/steps/22-app-stale-timer/src/) | [log](options-chain/22-app-stale-timer.txt), [full](options-chain/22-app-stale-timer-full.txt) |
| 23 the feed as one record | `verify` | ✔ VERIFIED 129/129 | [src](options-chain/steps/23-app-feed/src/) | [log](options-chain/23-app-feed.txt) |
| 24 three mutants | `verify` | ✔ VERIFIED 129/129: all three survive | [src](options-chain/steps/24-mutants/src/) | [log](options-chain/24-mutants.txt) |
| 25 stronger `place` contract | `verify` | ✗ the `place` mutant is caught (certificate still VERIFIED) | [src](options-chain/steps/25-mutants-place-spec/src/) | [log](options-chain/25-mutants-place-spec.txt) |
| 26 final | `verify` | ✔ VERIFIED 131/131 | [src](options-chain/steps/26-final/src/) | [log](options-chain/26-final.txt) |

The two `--full` logs are not part of the replay (it runs each step's command only).
