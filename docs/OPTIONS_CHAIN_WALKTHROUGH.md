# Walkthrough: building a verified options chain

This walkthrough builds `examples/options-chain`, a medium-complexity trading widget, with
vreact from an empty folder to a verified React app, and then grows it. "Verified" means that
every proof obligation of the app's specification is proved, with no trusted parts. The
specification does not say everything about the app; the end lists what it leaves out. Part 1 builds
the first version: model, reducer, components, a simulated market feed, and an audit of the
specification. Part 2 adds what a real app gets next: a rule checked where actions are
dispatched, a risk limit whose proof needs a hand-written Lean lemma, a reducer that owns the
rules of the feed, a move of the state onto Maps and Sets with generic helpers, two new
features, a second audit, and the answer to an outside review of the specification. The final
app has 6 components, 68 functions (the reducers among them) and 210 proof obligations (claims
the verifier must prove, Step 1a), plus a proof file of 8 Lean lemmas (helper theorems, Step
10). Its whole-app certificate (a theorem about every run of the app, Step 3) depends only on
Lean's three standard axioms. At the end we list exactly what is and is not proven.

It is written for a developer who knows React and TypeScript but has never used formal
verification. Each new idea is explained the first time it appears. Every tool output below
comes from a real run. The raw logs are in [`options-chain/`](options-chain/), and a full
snapshot of `src/` at each step is in [`options-chain/steps/`](options-chain/steps/).
[`options-chain/replay.sh`](options-chain/replay.sh) re-runs every step and checks that the tool
still says the same thing. A few outputs come from **probes**: single runs of a step's snapshot
with a small change, saved in [`options-chain/probes/`](options-chain/probes/) and not replayed.
A few checks were done by hand and have no saved log (the build and the browser sessions); the
text says so where they appear.
The snapshots are for `vreact verify` and the replay: they hold `src/` (and from step 27 on
`proofs/`) only, without the project's configs, and those before step 23 have no `styles.css`
(which `main.tsx` imports). The app you can run is
[`examples/options-chain`](../examples/options-chain/).

Two numberings run side by side. The snapshots and their logs are numbered 01 to 57; the text
has its own sections, Step 1 to Step 19. "Step 12", with a capital S, names a section of this
text; "step 33" (or "snapshot 33", "log 33") names a snapshot and its log.

> **Inspiration.** The feature set is modelled on the *Options Chain (new)* widget in the
> Trading Technologies documentation
> ([widget display](https://library.tradingtechnologies.com/trade/options/options-chain/description-options-chain/options-chain-new-widget-display/)).
> The component built here is an original, generic one. It is not that product and copies
> none of its branding, names or styling. The underlying "DIX" contract and all prices are
> made up.

---

## Contents

* [What we build](#what-we-build)
* [Setup](#setup)
* [Part 1: the first version](#part-1-the-first-version)
   * [Step 1: the model, spec first](#step-1-the-model-spec-first)
   * [Step 2: the reducer](#step-2-the-reducer)
   * [Step 3: the chain, top-down against trusted stubs](#step-3-the-chain-top-down-against-trusted-stubs)
   * [Step 4: an invariant that depends on props](#step-4-an-invariant-that-depends-on-props)
   * [Step 5: the children, one by one](#step-5-the-children-one-by-one)
   * [Step 6: the App and a moving market](#step-6-the-app-and-a-moving-market)
   * [Step 7: audit the spec with mutants](#step-7-audit-the-spec-with-mutants)
   * [Step 8: the app at the end of Part 1](#step-8-the-app-at-the-end-of-part-1)
* [Part 2: the app grows](#part-2-the-app-grows)
   * [Step 9: a precondition about the action](#step-9-a-precondition-about-the-action)
   * [Step 10: a cap on the open quantity, and the first Lean proof](#step-10-a-cap-on-the-open-quantity-and-the-first-lean-proof)
   * [Step 11: a Rally button](#step-11-a-rally-button)
   * [Step 12: the rules of the feed, in one reducer](#step-12-the-rules-of-the-feed-in-one-reducer)
   * [Step 13: the state on Maps and Sets](#step-13-the-state-on-maps-and-sets)
   * [Step 14: generic helpers](#step-14-generic-helpers)
   * [Step 15: watched strikes](#step-15-watched-strikes)
   * [Step 16: amending an order](#step-16-amending-an-order)
   * [Step 17: a second mutation audit](#step-17-a-second-mutation-audit)
   * [Step 18: an outside review](#step-18-an-outside-review)
   * [Step 19: the final app](#step-19-the-final-app)
* [What exactly is proven](#what-exactly-is-proven)
* [Where the tool pushed back](#where-the-tool-pushed-back)
* [Try it yourself](#try-it-yourself)
* [The steps and their logs](#the-steps-and-their-logs)

---

## What we build

An options chain shows the calls and puts of several expiries of one product, strike by strike,
around the price of the underlying futures contract. The finished widget looks like this
(a text sketch with illustrative numbers; the real one is an HTML table):

```
 Options chain · simulated futures move +3 ticks                      [Pause feed] [Rally]
 [DEC 26] [MAR 27] [JUN 27]  [Collapse all]  Strikes ± [3] 7 11 99 All  Heat 1 ticks [−][+]
 Watching [★ 96.00]
 ───────────── Calls ─────────────  Strike   ───────────── Puts ──────────────   Vol
  Qty   Bid     Ask     Qty                   Qty   Bid     Ask     Qty
 ▾ DIX DEC 26                        🔒        62    102.40  102.45  56            live
   88   6.45    6.80    40          ★ 96.00    95   0.75    0.95    61           23.0%  ← watched
  102   3.60    3.95    79          ☆ 99.00   145   2.65    2.95    20           21.9%
  …                                 ☆ 102.00 ← the at-the-money row, highlighted
 ▸ DIX MAR 27                        🔓        84    103.10  103.15  25     held 103.10
 ┌ Buy DIX DEC 26 102.00 C ───────────────────────────────┐
 │ Quantity [−] 1 [+] [1][5][10][25]   Price [−] 3.10 [+]  │
 │ Market 2.95 / 3.10       [Submit] [Cancel]             │
 └────────────────────────────────────────────────────────┘
 Working orders: Buy 5 DIX DEC 26 102.00 C @ 3.10 [▼][▲][Cancel]
```

### Feature mapping

| Feature of the inspiration | Here | Where |
|---|---|---|
| Expiry buttons that jump to the expiry's ATM strike | one button per expiry: it expands the expiry, locks it to the futures price, focuses it, and scrolls to its at-the-money row (`href="#atm-<id>"`) | `OptionsChain.tsx`, `jump` in `reducer.ts` |
| Term row: symbol, expiry, best bid/ask of the futures | `TermRow`; the futures bid/ask are clickable | `TermRow.tsx` |
| Lock icon: chain locked to the underlying price | 🔒 = the strike window follows the live futures price; click to **hold** it at the price of that moment (🔓); click again to lock it to the live price again | `holdAt` / `follow` in `reducer.ts` |
| Expand/collapse per expiry and for all expiries | ▾/▸ in the term row; "Collapse all" / "Expand all" | `toggle`, `setCollapsed` |
| Quick strike filter 3, 7, 11, 99, All | strikes within N rows of the ATM row, per expiry | `strikeWindow`, `shownRows` in `model.ts` |
| Rows: call market, strike in the middle, put market, volatility | `StrikeRow`; in-the-money cells shaded; the ATM row highlighted | `StrikeRow.tsx` |
| Heat map: approach / slight cross / larger cross, within a number of ticks | `heatOf`: `near` (blue), `cross` (light yellow), `deep` (dark yellow); threshold 1–5 ticks | `model.ts`, `styles.css` |
| Click a bid/ask (option or futures) to open a pre-filled order entry | `OrderTicket`: clicking a bid prepares a sell at the bid, an ask a buy at the ask; quantity and price adjustable; shows the live market and warns when the order would trade at once | `OrderTicket.tsx` |
| (orders) | working orders listed under the chain in the order they were placed, each repriced by one tick (▼/▲) or cancelled; 1–500 lots per order, at most 1000 lots working in total | `place` / `amend` / `cancel` in `reducer.ts` |
| (watched strikes) | ☆ in a strike cell watches that strike: it is shown in every expiry, whatever the filter; the toolbar lists the watched strikes | `watchStrike` in `reducer.ts`, `shownRows` in `model.ts` |
| (demo feed) | the App moves the futures prices; "Pause feed" stops them (a tick dispatched just before the click can still show after it), "Rally" makes them climb | `simReducer` in `App.tsx` |

**Out of scope.** The following are not built:

* **Greeks and theoretical pricing.** Theoretical values and volatilities are *input data*.
  The demo values were computed once, offline, with Black-76 and pasted as constants. Nothing
  about pricing is verified.
* **Option spreads** (the optional stretch goal). Not built.
* **The expiry selector itself.** Choosing which expiries are in the chain is the parent's job:
  the chain shows the expiries it is given, each with a button.
* **Real trading.** No order routing. "Working orders" are kept in the component's state, and
  are lost on reload.
* **A real market feed.** The App simulates one: two timers move the futures prices. Option
  quotes stay fixed in the demo.

### Prices are integers

Every price in the model is an `int`: a number of **ticks**. The demo tick is 0.05, so 102.40 is
2048. Why not `number`? A `number` is an IEEE double: `0.1 + 0.2 !== 0.3`. vreact treats
`number` as an opaque type: every operation on it is left uninterpreted, so that nothing false
about doubles can be proved, and proofs therefore know nothing about its values. Exchange
prices are tick-based anyway. A missing quote (no bid, no ask) is `null`, so a quote side has
type `int | null`. Volatility is an `int` in basis points, used for display only.

`int` comes from `vreact/spec`. For TypeScript and at runtime it is just `number`. The verifier
reads it as a mathematical integer, so integer code may use `+ - *` and comparisons. `/` would
give a `number`; integer division is `idiv(a, b)`, which rounds down.

---

## Setup

From a fresh clone (Node ≥ 22.6, Lean 4 via [elan](https://github.com/leanprover/elan)):

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain   # npm deps + Lean library
cd examples/options-chain
npx vreact verify          # ✔ VERIFIED 210/210
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
run as `node <repo>/vreact/bin/vreact.js …`. `npx vreact …` is the same program. All logs and
probe outputs were made with one version of vreact, the one in this repository.

The finished app has eight verified files and one proof file:

| file | what |
|---|---|
| `src/collections.ts` | generic helpers over Sets, Maps and lists, each proved once for every type its constraint allows (Part 2) |
| `src/model.ts` | types, the chain's data requirements, ATM strike, strike window, the rows an expiry shows, ITM test, heat map, order validation and the open quantity, formatting |
| `src/reducer.ts` | the UI state (Sets and Maps), its invariant, the operations and their frame conditions, the reducer |
| `src/OptionsChain.tsx` | the chain component |
| `src/TermRow.tsx` | one expiry's header row |
| `src/StrikeRow.tsx` | one strike row with its watch button, and `PriceCell` (a clickable bid/ask cell) |
| `src/OrderTicket.tsx` | the order entry |
| `src/App.tsx` | the demo data and the simulated futures feed, with its own reducer |
| `proofs/model.lean` | Lean lemmas about the open quantity, used by the proofs of the cap (Part 2) |

The app folder also has `lakefile.toml` and `lean-toolchain` (added in Part 2). They are only
for a Lean editor opened on the app folder, so that it can check `proofs/model.lean` against the
generated Lean; `vreact verify` does not need them. `setup.sh` leaves an existing
`lakefile.toml` alone. If that file lacks a `[[require]]` of the package `vts` at `.vreact`,
it prints a note that editor support needs one. The app's `lakefile.toml` has that entry, so
here it prints no note.

---

## Part 1: the first version

Steps 1–8 build the widget from the model up: the data and its contracts, the UI state and its
reducer, the chain against stubs of its children, the children, the App with a simulated feed,
and an audit of the specification. Part 1 ends at step 26 with 131 obligations, all proved.

---

## Step 1: the model, spec first

### 1a. Contracts before code ([log](options-chain/01-model-spec.txt), [snapshot](options-chain/steps/01-model-spec/src/))

We start with the data types and with **contracts**: machine-checked statements of what a
function needs (`requires`, its *precondition*) and what it promises (`ensures`, its
*postcondition*). The bodies we do not know yet are left as `hole<T>()`, a placeholder that the
synthesizer will try to fill.

```ts
/** A two-sided market: best bid and ask (ticks, null when there is none) and their quantities. */
export type Quote = {
  readonly bid: int | null;
  readonly bidQty: int;
  readonly ask: int | null;
  readonly askQty: int;
};

/** One strike of an expiry: the call and put markets, theoretical values, implied volatility. */
export type Strike = {
  readonly strike: int;
  readonly call: Quote;
  readonly put: Quote;
  readonly callTheo: int;
  readonly putTheo: int;
  readonly vol: int; // basis points, display only
};

/** One expiry: its futures market (the underlying) and its strike ladder (ascending). */
export type Expiry = {
  readonly id: int;
  readonly symbol: string;
  readonly label: string;
  readonly future: Quote;
  readonly strikes: readonly Strike[];
};

/** What the chain needs from its data: distinct expiry ids, distinct strikes in each expiry. */
export function validChain(es: readonly Expiry[]): boolean {
  return distinct(es, (e) => e.id) && es.every((e) => distinct(e.strikes, (s) => s.strike));
}
…
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
…
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
  src/model.ts:103:51 [index]: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first
pending (hole() / sorry): quotePrice, midPrice, strikeWindow, heatOf

◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)  5/6 obligations proved, 1 unchecked; components: 0/0 verified  (5.4s)
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
  candidate passes 206 random tests: q.ask   (2 candidate(s) tested in 0.0s)
  ✔ proved by Lean: quotePrice with q.bid / q.ask
hole in midPrice: int | null   scope: q, q.bid, q.bidQty, q.ask, q.askQty
  candidate passes 400 random tests: q.bid   (1 candidate(s) tested in 0.0s)
  ✔ proved by Lean: q.bid
hole in atmIndex: int   scope: ks, price
  23461 candidates tested in 60.0s, up to size 8; stopped: the 60s time limit was reached at size 8
  no verified solution for hole in atmIndex: no candidate passed the tests
  most common failure (23461×): price: postcondition fails on [[{"strike":2,"call":{"bid":-10,"bidQty":1,"ask":null,"askQty":2},"put":{"bid":2,"bidQty":7,"ask":-5,"askQty":-5},"callTheo":7,"putTheo":4,"vol":10}],10] ↦ 10
…
```

The test inputs are random, but reproducible: each hole's inputs come from a generator with a
fixed seed (`--seed N` picks another one; the default is 1), so a re-run tests the same inputs
and prints the same counterexamples. The search itself stops after 60 s per hole, so how many
candidates it reaches, and the timings, depend on the machine: a re-run will not print these
exact numbers. The verdicts and the fills are the same each time (the replay checks them).

`quotePrice` is filled as expected. The `midPrice` result is a warning: **`return q.bid`
satisfies its contract.** The first contract only said "null when both sides are missing" and
"within the spread", and the bid is within the spread. A verified function is only as good as
its specification, and the synthesizer just showed that ours does not say "mid".

For `atmIndex`, no candidate passed, not even the trivial `-1`. The reason is how synth tests:
it runs the contracts as JavaScript, where `implies(a, b)` is an ordinary function call that
evaluates `b` even when `a` is false. For `r = -1`, `ks[-1].strike` throws. (The failure printed
above is not that case. Synth counts the failures of all candidates by kind and shows the
first one of the most common kind. That is its first candidate, `price`: on a one-strike ladder
and the price 10, it returns 10, which is not even an index of the ladder.) In Lean, `implies`
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
spec. Both are fixed by saying what we mean ([log](options-chain/04-model-synth-strong.txt)).
`midPrice` is the mid, rounded down, of a two-sided market (`isMid`: `r === idiv(bid + ask, 2)`
when both sides exist), otherwise the side that is there; "within the spread" stays, as a
property the proof must also establish. For `atmIndex`, "-1 for none" must not be an escape
hatch:

```ts
// midPrice
  ensures((r: int | null) => isMid(q, r));
  ensures((r: int | null) => q.ask !== null || r === q.bid);
  ensures((r: int | null) => q.bid !== null || r === q.ask);
  ensures((r: int | null) => withinSpread(q, r));
…
// atmIndex
  // "-1 for none" must not be an escape hatch: a non-empty ladder always has an ATM row
  ensures((r: int) => implies(ks.length > 0, r >= 0));
```

```
$ vreact synth src/model.ts --write
…
  ✔ proved by Lean: quotePrice with q.bid / q.ask
hole in midPrice: int | null   …
…
  no verified solution for hole in midPrice: no candidate passed the tests
  most common failure (10143×): q.bid: postcondition fails on [{"bid":-10,"bidQty":1,"ask":0,"askQty":-10}] ↦ -10
…
wrote src/model.ts
```

`q.bid` is now refuted by a concrete input (a bid of −10 and an ask of 0: the mid, rounded down,
is −5, not −10). The rest needs branches, which synth does not build ("write this one by hand").
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
// strikeWindow
return { lo: Math.max(0, atm - levels), hi: Math.min(n, atm + levels) };
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
✗ src/model.ts:140:11  [postcondition] postcondition of strikeWindow: forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, levels))
…
4 obligation(s) not checked:
  src/model.ts:116:11 [postcondition], src/model.ts:119:44 [index], src/model.ts:119:11 [postcondition], src/model.ts:121:11 [postcondition]: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first

✗ NOT VERIFIED  16/24 obligations proved, 4 failed, 4 unchecked; components: 0/0 verified  (11.7s)
```

Some vocabulary first. vreact proves each obligation with `vreact_auto`, its automation, whose
main tool is `grind`, an automatic Lean **tactic** (a command that builds a proof, or a step of
one) for this kind of goal (equalities, linear arithmetic, case splits). "`grind` failed" means
it ran out of ideas, and the goal it prints is where it stopped. A failure does not stop the
check: vreact admits the failed goal (with `sorry`) and goes on, so one run reports every
failure.

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

✗ NOT VERIFIED  21/22 obligations proved, 1 failed; components: 0/0 verified  (5.9s)
```

The goal is the case of a non-empty ladder (`h₂₁`) in which `findIndex` found no nearest strike
and returned −1 (`h`). That case cannot happen: "a non-empty ladder has a nearest strike" is
true. But proving it is an **induction** over the list (a minimum exists): prove the claim for
the empty list, then show that adding one element keeps it true, which covers lists of every
length. The automation does not do induction. We state what is provable and still rules out
the escape hatch:

```ts
// "-1 for none" must not be an escape hatch: whenever some strike is nearest, an ATM row is
// found. (A non-empty ladder always has one; the prover cannot show that without induction.)
ensures((r: int) => implies(ks.some((s) => nearest(ks, s, price)), r >= 0));
```

`return -1` is now refuted too (synth's random tests and Lean both reject it), and the chain
handles `-1` anyway (Step 3).

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

✔ VERIFIED  22/22 obligations proved; components: 0/0 verified  (5.9s)
```

`heatOf` and `midPrice` were right the first time. The verifier checked, for example, that
`idiv(b + a, 2)` always lies between bid and ask when `b ≤ a`.

---

## Step 2: the reducer

The UI state lives in one record, managed by `useReducer`. Its **invariant** is a property that
must hold in *every* state the component can ever reach. Here it says that the heat threshold
is valid and that every working order is valid, with distinct ids below `nextId`
([snapshot](options-chain/steps/12-reducer-verified/src/reducer.ts)):

```ts
/** An unlocked expiry: its strike window stays centred on the price captured when it was unlocked. */
export type Hold = { readonly expiry: int; readonly price: int };

export type ChainUi = {
  readonly collapsed: readonly int[]; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly held: readonly Hold[]; // unlocked expiries; the others follow the futures price
  readonly focus: int | null; // the expiry last jumped to
  readonly heat: int; // heat-map threshold, in ticks
  readonly orders: readonly Order[]; // working orders
  readonly nextId: int;
};

/** The UI-state invariant: a valid heat threshold, valid working orders with fresh, distinct ids. */
export function wellFormed(u: ChainUi): boolean {
  return (
    1 <= u.heat &&
    u.heat <= MAX_HEAT &&
    distinct(u.orders, (o) => o.id) &&
    u.orders.every((o) => validOrder(o) && o.id < u.nextId)
  );
}
```

A reducer must be **total**: no `requires`. React may apply an action to any queued state, so
every operation must keep the invariant from any well-formed state, and say so:
`ensures((r) => implies(wellFormed(u), wellFormed(r)))`. Each operation is `@opaque`, so the
reducer and the components reason with the contracts only. The reducer is a `switch` over a
discriminated-union `Action` (one variant per operation) that delegates to them. (Step 9
relaxes the first rule: a reducer may have a `requires` that mentions only the action.)

### 2a. Synthesis finds three weak specs ([log](options-chain/08-reducer-synth.txt))

```
$ vreact synth src/reducer.ts
hole in setCollapsed: ChainUi   …
  candidate passes 400 random tests: { ...u, collapsed: ids }   (14 candidate(s) tested in 0.1s)
  ✔ proved by Lean: { ...u, collapsed: ids }
hole in setFilter: ChainUi   …
  candidate passes 400 random tests: { ...u, filter: f }   (17 candidate(s) tested in 0.1s)
  ✔ proved by Lean: { ...u, filter: f }
hole in holdAt: ChainUi   …
  candidate passes 400 random tests: { ...u, held: [{ expiry: id, price: price }] }   (12658 candidate(s) tested in 32.3s)
  ✔ proved by Lean: { ...u, held: [{ expiry: id, price: price }] }
hole in follow: ChainUi   …
  candidate passes 400 random tests: jump(u, id)   (17 candidate(s) tested in 0.0s)
  ✔ proved by Lean: jump(u, id)
hole in place: ChainUi   …
  23653 candidates tested in 60.0s, up to size 6; stopped: the 60s time limit was reached at size 6
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
`cancel` ([snapshot](options-chain/steps/09-reducer-synth-strong/src/reducer.ts)):

```ts
/** Frame condition: the same expiries are collapsed, same filter, focus and heat threshold. */
export function sameView(u: ChainUi, r: ChainUi): boolean { … }
…
/** Frame condition: every hold of another expiry than `id` is kept. */
export function keepsHolds(u: ChainUi, r: ChainUi, id: int): boolean { … }
…
// holdAt and follow
  ensures((r: ChainUi) => sameView(u, r) && keepsHolds(u, r, id));
…
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
  candidate passes 400 random tests: { ...u, held: u.held.filter((x) => x.expiry !== id) }   (9690 candidate(s) tested in 26.0s)
  ✔ proved by Lean: { ...u, held: u.held.filter((x) => x.expiry !== id) }
…
hole in cancel: ChainUi   …
  candidate passes 400 random tests: { ...u, orders: u.orders.filter((x) => x.id !== id) }   (12887 candidate(s) tested in 34.7s)
  ✔ proved by Lean: { ...u, orders: u.orders.filter((x) => x.id !== id) }
wrote src/reducer.ts
```

Both are the intended programs. With the frame conditions in place, synth's answer is the right
one. `holdAt` and `place` are not found within the 60 s that synth spends on each hole.

Snapshot 10 runs the same search with `chainReducer` removed
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
`place` validates and appends ([snapshot](options-chain/steps/11-reducer-bug/src/reducer.ts)).
Besides keeping the invariant, its contract promises that a valid order with the next id, the
quantity and the price is added:

```ts
  ensures((r: ChainUi) => implies(validQty(qty) && price > 0, r.orders.some((o) => o.id === u.nextId && o.qty === qty && o.price === price)));
  if (!validQty(qty) || price <= 0) return u;
  const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: [...u.orders, o] };
```

(This contract says nothing about the order's contract, strike or direction, and has no frame
condition. Step 7 shows what that lets through.)

```
$ vreact verify
…
✗ src/reducer.ts:136:11  [postcondition] postcondition of place: implies(wellFormed(u), wellFormed(r))
    │ …
    │ h_2 :
    │   x ∈ u.orders ∨
    │     x =
    │       { id := u.nextId, expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.ask,
    │         qty := qty, price := price }
    │ h_6 : -1 * x.id + u.nextId ≤ 0
…
✗ NOT VERIFIED  43/44 obligations proved, 1 failed; components: 0/0 verified  (10.3s)
```

The counterexample is the new order `x` itself, whose id is `u.nextId`: `nextId` was never
advanced, so the next order would reuse the id. The fix is `nextId: u.nextId + 1`:

```
✔ VERIFIED  44/44 obligations proved; components: 0/0 verified  (8.6s)
```

---

## Step 3: the chain, top-down against trusted stubs

We write the parent for real before its children exist. Each child is a **trusted stub**: its
props type and its contract, a placeholder body, and `@trusted`. `@trusted` means "do not verify
this body, assume the contract". vreact then verifies the parent *relative to* the children's
contracts, and reports exactly what is assumed. The stub of `StrikeRow`
([snapshot](options-chain/steps/15-chain-topdown/src/StrikeRow.tsx)):

```tsx
/**
 * One strike: call market | strike | put market | volatility.
 * Clicking a bid or an ask reports exactly the price shown in that cell.
 * @trusted — stub: contract only, implementation pending
 */
export function StrikeRow(props: StrikeRowProps) {
  requires(props.heat >= 1);
  callbackRequires(props.onPick, (right, side, price) => quotePrice(legOf(props.strike, right), side) === price);
  return (
    <tr className="todo-stub">
      <td>StrikeRow</td>
    </tr>
  );
}
```

`requires` on a component is what every parent must establish for its props: here, a valid
heat threshold. `callbackRequires` is the child's promise about the arguments it passes to a
callback prop. Here: whenever `StrikeRow` calls `onPick(right, side, price)`, `price` is the
current quote of that strike's call or put (`right`) on that side. The parent may rely on it,
and the child is checked against it. Note what it does not say: *which* cell was clicked. The
stub's comment promises more than its contract; Step 7 comes back to this. `TermRow` promises
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
    const center: int | null = held === null ? live : held;
    const n = e.strikes.length;
    const atm = center === null ? -1 : atmIndex(e.strikes, center);
    const span: Span = levels === null ? { lo: 0, hi: n } : strikeWindow(n, atm, levels);
    const rows = e.strikes.slice(span.lo, span.hi);
    …
    return (
      <tbody key={e.id}>
        <TermRow
          expiry={e}
          open={open}
          held={held}
          focused={ui.focus === e.id}
          onToggle={() => dispatch({ kind: "toggle", expiry: e.id })}
          onLock={() => {
            if (held !== null) dispatch({ kind: "follow", expiry: e.id });
            else if (live !== null) dispatch({ kind: "hold", expiry: e.id, price: live });
          }}
          onPick={(side, price) => {
            if (price > 0) setTicket({ expiry: e.id, leg: "future", strike: 0, side: side, price: price });
          }}
        />
        {open &&
          rows.map((s) => (
            <StrikeRow
              key={s.strike}
              strike={s}
              price={live}
              …
              heat={ui.heat}
              onPick={(right, side, price) => {
                if (price > 0) setTicket({ expiry: e.id, leg: legFor(right), strike: s.strike, side: side, price: price });
              }}
            />
          ))}
      </tbody>
    );
  })}
```

`center` is the price the strike window is centred on: the live price while the expiry is
locked, the held price once it is unlocked.

A quick rejection came first. VTS does not unify a ternary whose branches are `int | null` and a
narrowed `int` ([log](options-chain/13b-chain-ternary-rejected.txt)): `✗ VTS
src/OptionsChain.tsx:98:42: type mismatch: expected int, got int | null`. The annotation `const
center: int | null` above fixes that. Snapshot 13, one draft earlier, also used the
filter value itself as the key of its button: `key={f}`, where `f` is an *enum* (VTS's name for
a string-literal union type such as `StrikeFilter = "s3" | "s7" | "s11" | "s99" | "all"`). When
this walkthrough was first written, VTS rejected that (`keys must be int or string`), and the
filter buttons got `key={filterLabel(f)}`. vreact now accepts an enum key (the key is its
string), so snapshot 13 now stops at the same ternary as snapshot 13b
([log](options-chain/13-chain-key-rejected.txt)). `key={filterLabel(f)}` stays; either key
works. Then the first real result ([log](options-chain/14-chain-atm-edge.txt)):

```
$ vreact verify
…
✗ src/OptionsChain.tsx:101:67  [precondition] precondition of strikeWindow(n, atm, levels)
    │ `grind` failed
    │ case grind.1.1.1.1.1
    │   … (15 earlier hypotheses: E, props, κ, σ, ui, ticket, levels, allOpen, …: --full shows them)
    │ center, atm := …  (2 definitions, 8 lines: --full shows them)
    │ h₁₀, hpre, hinv, heq, h₈, h_5 : …  (6 long hypotheses, 39 lines: --full shows them)
    │ hcontract : …  (a contract instance, 3 lines: --full shows it)
    │ h : (JS.findIndex e.strikes fun s => model.nearest e.strikes s held_1) + 1 ≤ 0
    │ …
    │ h₂₂ h_7 : σ.ui.filter = model.StrikeFilter.s3
    │ …
    │ ⊢ False
✗ src/OptionsChain.tsx:101:67  [precondition] precondition of strikeWindow(n, atm, levels)
    │ …

1 obligation(s) not checked:
  src/OptionsChain.tsx:107:20 [unique-keys]: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first
…
✗ NOT VERIFIED  72/75 obligations proved, 2 failed, 1 unchecked; components: 0/5 verified  (61.0s)
```

The short report prints at most 18 lines of each failure, always ending with the goal's
conclusion `⊢ …`. This goal is much longer, so the report shortens it, and every line that
stands for others names them and ends in "--full shows …". The hypotheses farthest from the
conclusion are left out (the first line names them). Long ones are folded into one line each:
the two local definitions `center` and `atm`, six long hypotheses, and a **contract instance**
(`hcontract`: what the `ensures` of a function in the goal says about these arguments). The
short hypotheses next to the conclusion stay whole, and here they are the interesting part.
`vreact verify --full` prints the goal whole ([log](options-chain/14-chain-atm-edge-full.txt)).
Its key lines, from the first goal:

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
```

Read together: `heq` (folded in the short report, elided here: it spells out `held` and `live`)
ends in `= some held_1`, so the center is some price `held_1`; `h` says `atmIndex` returned −1
(the `findIndex` result plus 1 is at most 0); and `h₂₂ h_7` (two hypotheses with the same
statement) say that the filter is "3". `atmIndex`'s contract allows −1 when no strike is nearest,
which is the case for an empty ladder. The code shows a second way to get −1:
`center` is `null` when there is no price at all (no bid, no ask, nothing held). Either way
`strikeWindow`'s precondition `0 <= atm` fails. This is the **ATM at the edge, one level up**.

Why is the same call reported twice? The translation evaluates the `map` callback over the
expiries twice: once to compute each `<tbody>`'s key, and once to build its rows. The second
goal is the same case, with one more fact (`hmem₁₃ : e ∈ props.expiries`). For the same
reason, the obligation that the `<tbody>` keys are distinct (line 107) is not checked: the keys
are computed through the failed call, so its goal contains the `sorry` that stands for it.

The fix is the first condition below ([log](options-chain/15-chain-topdown.txt)):

```tsx
// no ATM row (empty ladder, or no price at all) or "All": show every strike
const span: Span = atm < 0 || levels === null ? { lo: 0, hi: n } : strikeWindow(n, atm, levels);
```

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

✔ VERIFIED modulo @trusted declarations  75/75 obligations proved; components: 0/5 verified  (18.3s)
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
export const EXPIRIES: readonly Expiry[] = [
  {
    id: 1,
    symbol: "DIX",
    label: "DEC 26",
    …
];
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
  <OrderTicket
    …
    title={`${tExp!.symbol} ${tExp!.label} ${contractText(ticket.leg, ticket.strike)}`}
    market={marketOf(tExp!, ticket)}
```

([log](options-chain/16-props-stability.txt))

```
$ vreact verify
…
✗ src/OptionsChain.tsx:32:17  [props-stability] OptionsChain: invariant survives a re-render with new props (state is preserved)
    │ `grind` failed
    │ …
    │ props props' : Props
    │ σ : State
    │ h, h_1 : …  (2 long hypotheses, 12 lines: --full shows them)
    │ ticket : Option model.Ticket
    │ ticket_1 : model.Ticket
    │ heq : σ.ticket = some ticket_1
    │ h_2 : ∀ (a : model.Expiry), a ∈ props'.expiries → ¬a.id = ticket_1.expiry
    │ …
    │ w : model.Expiry
    │ left : w ∈ props.expiries
    │ right : w.id = ticket_1.expiry
    │ …
✗ NOT VERIFIED  77/78 obligations proved, 1 failed; components: 0/5 verified  (27.8s)
```

The handlers do establish the invariant: the `tExp!` assertions and every `setTicket` were
proved. The failure is about something else. When the parent re-renders with new props, **React
keeps the component's state**. The goal has the old `props` and new props `props'`, which
satisfy only the precondition. `heq` says that a ticket is open. `w`, `left` and `right` say
that the old props list its expiry, and `h_2` that no expiry of the new props has its id.
Nothing stops the feed from dropping the expiry, for example when it expires, while a ticket for
it is open. An invariant that ties state to props cannot survive that, and the verifier checks
this case for every component (the `[props-stability]` obligation).

The fix the skill recommends is to keep the invariant about state only, look the expiry up at
render time, and clamp ([log](options-chain/17-props-clamped.txt)):

```tsx
// the ticket's expiry, looked up in the current props: it may have been delisted meanwhile
const tExp = ticket === null ? undefined : props.expiries.find((e) => e.id === ticket.expiry);
…
{ticket !== null && tExp !== undefined && (
  <OrderTicket
    …
    title={`${tExp.symbol} ${tExp.label} ${contractText(ticket.leg, ticket.strike)}`}
    market={marketOf(tExp, ticket)}
    …
  />
)}
{ticket !== null && tExp === undefined && (
  <div className="ticket gone">
    <p>This contract is no longer listed.</p>
    <button onClick={() => setTicket(null)}>Close</button>
  </div>
)}
```

```
✔ VERIFIED modulo @trusted declarations  76/76 obligations proved; components: 0/5 verified  (21.2s)
```

The same reasoning is why the reducer's invariant says nothing about the expiries:
`collapsed` and `held` may name expiries that are gone, and the chain only looks them up.

---

## Step 5: the children, one by one

### 5a. StrikeRow ([log](options-chain/18-strikerow-bug.txt), [log](options-chain/19-strikerow.txt))

`StrikeRow.tsx` also gets `PriceCell`, one clickable bid or ask, whose contract is the smallest
possible promise:

```tsx
/** One bid or ask cell. Clicking it reports exactly the price it shows; an empty cell has no button. */
export function PriceCell(props: PriceCellProps) {
  callbackRequires(props.onPick, (p) => props.price === p);
  const p = props.price;
  const cls = props.itm ? "px itm" : "px";
  if (p === null) return <td className={cls}>–</td>;
  return (
    <td className={`${cls} heat-${props.heat}`}>
      <button onClick={() => props.onPick(p)}>{fmtPrice(p)}</button>
    </td>
  );
}
```

`StrikeRow` renders four of them, two for the call and two for the put. Its own contract
(`quotePrice(legOf(strike, right), side) === price`) must follow from each cell's contract. The
first version had a copy-paste error that is easy to miss in a mirrored layout
([snapshot](options-chain/steps/18-strikerow-bug/src/StrikeRow.tsx)):

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
    │ x : Int
    │ hpre : props.heat ≥ 1
    │ hcb₁₂ : props.strike.put.bid = some x
    │ …
    │ h_1 : ¬props.strike.put.ask = some x
    │ …
✗ NOT VERIFIED  97/98 obligations proved, 1 failed; components: 1/6 verified  (24.5s)
```

A **callback-contract** obligation says that a call of a callback prop satisfies its
`callbackRequires`. Line 55 is the put **bid** cell, which reports `"ask"`. Clicking a put's bid
would have opened a *buy* ticket at the *bid* price. The contract catches this because the
report contradicts itself: the bid's price under the name "ask". In the goal, `hcb₁₂` (what
`PriceCell` promises about its callback) says that the reported `x` is the put's bid, and
`h_1` that the put's ask, the quote the report names, is not `x`. (A cell that reported another
cell's name together with that cell's price would not contradict itself; Step 7 comes back to
that.) The chain and the App are `INCOMPLETE` too, although all their own obligations are
proved: they use `StrikeRow`, so they rest on the `sorry` that admits its failed obligation (the
certificate lists it among its axioms as `sorryAx`). After the fix (`"bid"`), `StrikeRow` and
`PriceCell` are `VERIFIED`, and the chain and the App are back to `VERIFIED*`: `✔ VERIFIED
modulo @trusted declarations  98/98 obligations proved; components: 2/6 verified`.

### 5b. TermRow and OrderTicket ([log](options-chain/20-children-bug.txt), [full log](options-chain/20-children-bug-full.txt), [log](options-chain/21-children-verified.txt))

`TermRow` reuses `PriceCell` for the futures bid and ask, and verifies on the first try (12/12).
`OrderTicket` has its own state, initialised from the clicked cell, and an invariant over it
([snapshot](options-chain/steps/20-children-bug/src/OrderTicket.tsx)):

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
    │ marketable := …  (a definition, 4 lines: --full shows it)
    │ e : DomEvent
    │ hinv : (1 ≤ σ.qty ∧ σ.qty ≤ 500) ∧ σ.price > 0
    │ h : σ.price + -1 ≤ 0
    │ ⊢ False

✗ NOT VERIFIED  121/122 obligations proved, 1 failed; components: 3/6 verified  (22.0s)
```

At a price of 1 tick, "−" makes it 0. A **handler** obligation says that a click, run against
the state the user saw, keeps the invariant. `h` says `σ.price - 1 ≤ 0`, and `hinv` says the
price is positive, so the price is 1. To keep the report within its 18 lines, the definition of
`marketable` is folded into one line (it plays no part here); the full goal is in the
[full log](options-chain/20-children-bug-full.txt). The fix is a guard, and the button is
disabled for good measure
([snapshot](options-chain/steps/21-children-verified/src/OrderTicket.tsx)):

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
…
✔ VERIFIED  122/122 obligations proved; components: 6/6 verified  (22.0s)
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
props-stability work of Step 4 matters now. First draft
([snapshot](options-chain/steps/22-app-stale-timer/src/App.tsx)):

```tsx
const [offset, setOffset] = useState<int>(0);
const [seed, setSeed] = useState<int>(1);
const [paused, setPaused] = useState<boolean>(false);
invariant(-MAX_MOVE <= offset && offset <= MAX_MOVE);
invariant(0 <= seed && seed < 65537);
// every 0.8 s the futures move by -2..+2 ticks, staying within ±MAX_MOVE
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
    │ h, h_5, h_6, h_9 : …  (4 long hypotheses, 116 lines: --full shows them)
    │ s : State
    │ left : -1 * s.offset + -40 ≤ 0
    │ left_1 : s.offset + -40 ≤ 0
    │ left_2 : -1 * s.seed ≤ 0
    │ right_2 : s.seed + -65536 ≤ 0
    │ h_3 : (List.foldl (fun s u => u s) s (t e).updates).offset + 41 ≤ 0
    │ h_4 : ¬σ.paused = true
    │ …
    │ ⊢ False

✗ NOT VERIFIED  127/128 obligations proved, 1 failed; components: 5/6 verified  (50.1s)

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

`t` is the timer callback, `h` in the short report, folded there and printed whole by `--full`.
Its first branch is the effect's `if (paused) return;`, and the long elided expressions are
`move`, computed from `σ.seed`. The guard compares `σ.offset + move` with −40 and 40, but the
second update sets `offset := τ.offset + move`. The timer callback is a **stale closure**: its
guard reads `σ.offset` from the render that created the timer, but its update `o => o + move` is
applied to `τ`, the state React holds when it processes the update. vreact's model (see
`vreact/docs/SEMANTICS.md` §2.2) treats effects and timers as running later, against any state
that satisfies the invariant. So it asks for an **effect-robust** update: one that keeps the
invariant from *every* valid `τ`, not just from the snapshot. In the short report, `s` is such a
state: its feed is valid (`left` to `right_2`), and `h_3` says that after the timer's updates
its offset is at most −41. For example, the snapshot shows −38 and the move is −2, so the guard
passes, but by the time the update runs the offset is −40, and −40 − 2 = −42.

The fix the skill recommends: put the related state in one record, and make the timer apply one
total function to whatever state it finds ([log](options-chain/23-app-feed.txt)):

```ts
/** The simulated feed: how far the futures have moved, and the generator's state. */
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
const [paused, setPaused] = useState<boolean>(false);
invariant(validFeed(feed));
// every 0.8 s the futures move by -2..+2 ticks; the update reads the state it is applied to
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

✔ VERIFIED  129/129 obligations proved; components: 6/6 verified  (22.8s)
```

`moveFutures(EXPIRIES, offset)` maps over the constant, and its `ensures` (validity is preserved)
gives the chain its precondition on every tick.

After step 22 we also tuned the demo data and one default. The generated quotes had been too
close to their theoretical values, so most cells lit up in the heat map. The data was
regenerated with realistic spreads, and the default threshold went from 2 ticks to 1. Snapshots
23 to 26 use the tuned version. Earlier snapshots keep the earlier numbers.

---

## Step 7: audit the spec with mutants

Everything verifies. But Step 2 showed that a verified function is only as good as its
contract, and the same holds for the whole app. A cheap way to probe a spec is to break the
code on purpose and see whether the verifier notices. A change that still verifies (a
*surviving mutant*) shows something the spec does not say.

### 7a. Three mutants survive ([log](options-chain/24-mutants.txt), [snapshot](options-chain/steps/24-mutants/src/))

Three one-line changes to the app as it stands after Step 6 (snapshot 23), each a plausible bug
in a trading widget:

```tsx
// StrikeRow.tsx, the call-bid cell: report the put's ask instead
<PriceCell price={s.call.bid} … onPick={(x) => { if (s.put.ask !== null) props.onPick("put", "ask", s.put.ask); }} />
// TermRow.tsx, the futures-bid cell: report the futures ask instead
<PriceCell price={f.bid} … onPick={(x) => { if (f.ask !== null) props.onPick("ask", f.ask); }} />
// reducer.ts, place: every order goes in the wrong direction
const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "bid", qty: qty, price: price };
```

```
$ vreact verify
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
…
✔ VERIFIED  129/129 obligations proved; components: 6/6 verified  (22.8s)
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

**The `place` mutant is a weak spec.** `place`'s contract (Step 2c) promises only an order with
the next id, the quantity and the price. The expiry, the contract, the strike and the
direction were left open, so an app that sells when the ticket says "Buy" still verifies.
This is the lesson of Step 2 again, and here it matters most: the direction of an order. The
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
✗ src/reducer.ts:175:11  [postcondition] postcondition of place: implies(validQty(qty) && price > 0, r.orders.some((o) => orderFor(o, u.nextId, t, qty, price)))
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

✗ NOT VERIFIED  130/131 obligations proved, 1 failed; components: 6/6 verified  (22.9s)
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

### 7b. The end of Part 1 ([log](options-chain/26-final.txt), [snapshot](options-chain/steps/26-final/src/))

Snapshot 26 removes the mutants and keeps the stronger `place` contract. Three small edits
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

✔ VERIFIED  131/131 obligations proved; components: 6/6 verified  (22.8s)
```

---

## Step 8: the app at the end of Part 1

This is the app Part 1 set out to build. Before it grew, it was checked beyond the verifier
(Step 19b repeats these checks for the final app):

* **Verification.** `✔ VERIFIED 131/131` ([log](options-chain/26-final.txt)). The certificate's
  axioms are exactly `propext, Classical.choice, Quot.sound`. No `@trusted`, no `assume`, no
  `sorry` and no `hole` anywhere. `vreact synth src/model.ts` and `vreact synth src/reducer.ts`
  both report `no hole<T>() in …` ([probe](options-chain/probes/26-no-holes/)).
* **TypeScript.** `npx tsc --noEmit -p .` reports no errors.
* **The app runs** (checked by hand; no log of it is saved). With `npx vite`, curl got HTTP 200
  for the page and for every module (`main.tsx`, `App.tsx`, `OptionsChain.tsx`, `StrikeRow.tsx`,
  `TermRow.tsx`, `OrderTicket.tsx`, `model.ts`, `reducer.ts`, `styles.css`). In a browser,
  clicking the 2.95 call bid of DIX DEC 26 102.00 opened "Sell DIX DEC 26 102.00 C" at 2.95
  with the "Marketable" warning, and Submit listed "Sell 1 DIX DEC 26 102.00 C @ 2.95" under
  working orders. The console showed no errors. The server was then stopped.

**Not proven at the end of Part 1.** Part 2 comes back to this list; the final list is under
"What exactly is proven".

* That a click reports the cell that was clicked (Step 7a), and that the content on screen
  matches the data: the numbers in the right columns and colours, the ticket's "Buy"/"Sell"
  title. Rendering is proved not to fail, but what it shows is not specified.
* That `toggle`, `setCollapsed`, `setFilter`, `jump` and `setHeat` leave the rest of the state
  alone. Their contracts say what they change, and have no frame conditions.
* That `nextId` only grows. Only collisions with working orders are excluded, so nothing
  proves that the id of a cancelled order is never given to a new one.
* That a nearest strike always exists for a non-empty ladder (true, but it needs induction,
  Step 1d). The UI falls back to showing every strike if `atmIndex` ever returned −1.
* That the strikes are ascending. Nothing depends on it except the display order.
* That the ticket resets when another cell is clicked. This is done with a `key`, which is not
  verified.
* Anything about theoretical values, volatilities or the demo data, beyond `validChain`.
* Integer overflow: `int` is unbounded in the model. The values here are far below 2^53.

---

## Part 2: the app grows

A verified app is not finished when it first verifies: it gets new rules, new features and
better data structures, and each change must verify too. Part 2 grows the app of step 26 in
eleven more sections, Step 9 to Step 19, with snapshots 27 to 57. Steps 9–12 add a precondition
on dispatched actions, a cap on the open quantity with the walkthrough's first Lean proof, a
Rally button for the simulated feed, and a reducer that owns the rules of that feed. Steps 13–17
move the UI state onto Maps and Sets, write the comparisons they need once, as generic helpers,
add watched strikes and order amendment, and audit the specification a second time. Step 18
answers an outside review of the specification, and Step 19 is the final app. From step 27
on, every snapshot also holds `proofs/`, the app's proof file (in steps 27–29 it has no
lemmas).

Where snapshots 27–36 come from: they follow six commits in which the app's author extended the
app (and, in the first one, vreact), and each is the app's `src/` and `proofs/` at a commit.
Snapshot 27 is a commit as it was, with a deliberate break that the next commit fixes. The
other bug snapshots of that range put one plausible mistake back into the commit that follows
them: 29 is the cap commit with the proof file as it was before it (no lemmas); 31 is a first
draft of the rally effect's interval callback, and 33 of `simReducer` (each with the comment
above it reworded to describe the draft); 35 is the last commit with one condition missing
from one `case`.

---

## Step 9: a precondition about the action

Part 1 said that a reducer must be total: no `requires`, because React may apply an action to
any queued state. So `place` checked the quantity at run time and silently ignored a bad one.
But `OrderTicket` already promises valid quantities
(`callbackRequires(props.onSubmit, (qty, price) => validQty(qty) && price > 0)`), so a bad
quantity at the reducer can only come from a bug in the code between the ticket and the
reducer. The first change after Part 1 was to vreact itself, so that such a bug is found
before the app runs.

**A precondition about the action.** A reducer may now have a `requires`, as long as it
mentions only the action. React keeps a dispatched action in the hook's queue and passes that
same value to every call of the reducer, also when it applies the queue again (rebasing) or
calls the reducer twice (StrictMode in development). The *state* is whatever React holds when
it applies the action, which the dispatching handler cannot see. So a fact about the action can
be proved where the action is built, from the values the handler sees, and it then holds for
every state the action is applied to. Each `dispatch(a)` therefore becomes a **precondition
obligation at the dispatch site**. A `requires` that mentions the state is rejected before Lean
runs, with the reason (here for `requires(validAction(a) && wellFormed(u))`, a
[probe](options-chain/probes/28-requires-on-state/), not one of the steps): "the reducer
chainReducer's requires(…) may mention only the action, not the state u: React may apply a
queued action to any state, so it is checked at each dispatch from the action alone (put facts
about the state in the component's invariant)".

The reducer and `place` now say what an action must satisfy
([snapshot](options-chain/steps/27-action-precondition-bug/src/reducer.ts)):

```ts
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  requires(validQty(qty));
  …
/** What every dispatched action must satisfy: an order is for a valid quantity. */
export function validAction(a: Action): boolean {
  return a.kind === "place" ? validQty(a.qty) : true;
}

/**
 * Total over states: every valid action keeps the invariant. Validity of the action is a
 * precondition, so it is proved at every dispatch(…) site, not checked at run time.
 */
export function chainReducer(u: ChainUi, a: Action): ChainUi {
  requires(validAction(a));
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  …
```

The same commit adds `MAX_OPEN` and an `@opaque` function `openQty` to `model.ts`. Step 10 uses
them; until then they only show up as one more VERIFIED function in the report.

### 9a. A wrong quantity at the dispatch ([log](options-chain/27-action-precondition-bug.txt), [full log](options-chain/27-action-precondition-bug-full.txt), [snapshot](options-chain/steps/27-action-precondition-bug/src/))

To see the new check fire, the commit breaks the chain's submit callback on purpose:

```tsx
onSubmit={(qty, price) => {
  dispatch({ kind: "place", ticket: ticket, qty: qty - 1, price: price });
  setTicket(null);
}}
```

```
$ vreact verify
…
  INCOMPLETE         OptionsChain           src/OptionsChain.tsx:32
      ↳ an obligation of it failed
  INCOMPLETE         App                    src/App.tsx:115
      ↳ it uses OptionsChain (src/OptionsChain.tsx), which is not verified: an obligation of it failed
…
  ✗ src/OptionsChain.tsx                     35/37  (1 not checked)
  ✓ src/App.tsx                              12/12

Failed obligations
✗ src/OptionsChain.tsx:151:13  [precondition] precondition of chainReducer(…, { kind: "place", ticket: ticket, qty: qty - 1, price: price })
    │ `grind` failed
    │ …
    │ τ : State
    │ hcb₃₅ : (1 ≤ qty ∧ qty ≤ 500) ∧ 0 < price
    │ h : qty + -1 ≤ 0
    │ …
    │ ⊢ False

1 obligation(s) not checked:
  src/OptionsChain.tsx:150:11 [callback]: it depends on `sorry` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first

✗ NOT VERIFIED  140/142 obligations proved, 1 failed, 1 unchecked; components: 4/6 verified  (28.7s)
```

The failure is reported at the `dispatch` (line 151), not inside the reducer, and its
description shows the action as written, `qty: qty - 1` included. `hcb₃₅` is what `OrderTicket`
promises about the arguments of `onSubmit` (its `callbackRequires`): a quantity of 1 to 500 lots
and a positive price. `h` says `qty ≤ 1`. Together: `qty = 1`. (The other hypotheses describe
the open ticket; the [full log](options-chain/27-action-precondition-bug-full.txt) prints them
all.) The smallest order the ticket allows, one lot, reaches the reducer as `qty - 1 = 0` lots,
and `validQty(0)` is false. Without the new precondition, the same bug would have verified:
`place` ignores an invalid quantity at run time, so a one-lot order would silently not be
placed. The user clicks Submit, the ticket closes, and no working order appears.

The second obligation, "not checked" (`[callback]`), is the callback's own one (that it keeps
the chain's invariant, at line 150). Its goal contains the failed proof, which Lean replaces
with `sorry`, so it cannot be checked on its own. The App is INCOMPLETE because it uses the
chain, and its certificate shows `sorryAx`.

### 9b. The fix ([log](options-chain/28-action-precondition.txt), [snapshot](options-chain/steps/28-action-precondition/src/))

The next commit restores `qty: qty`:

```
$ vreact verify
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           25/25
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     37/37
  ✓ src/App.tsx                              12/12

✔ VERIFIED  142/142 obligations proved; components: 6/6 verified  (26.8s)
```

There are 11 obligations more than at step 26. Ten are the preconditions of the ten
`dispatch(…)` calls in `OptionsChain.tsx` (27 → 37). Nine of them are immediate, since
`validAction` is true for every kind but `"place"`; the tenth is the one that failed above, and
`OrderTicket`'s promise proves it. The eleventh is in the reducer (24 → 25): `chainReducer`
calls `place`, whose new `requires(validQty(qty))` is proved in the `"place"` case from
`validAction(a)`. So no dispatch in the app can hand the reducer an order of 0 or 501 lots.

---

## Step 10: a cap on the open quantity, and the first Lean proof

Next, a risk limit: all working orders together may hold at most
`MAX_OPEN = 1000` lots. The limit goes into the invariant, and `place` accepts an order only if
it keeps the total within the limit
([snapshot](options-chain/steps/30-open-cap/src/reducer.ts)):

```ts
// model.ts
export const MAX_OPEN: int = 1000;

/** Total quantity of the working orders. @opaque */
export function openQty(os: readonly Order[]): int {
  return os.reduce((n, o) => n + o.qty, 0);
}

// reducer.ts
export function wellFormed(u: ChainUi): boolean {
  return (
    1 <= u.heat &&
    u.heat <= MAX_HEAT &&
    distinct(u.orders, (o) => o.id) &&
    u.orders.every((o) => validOrder(o) && o.id < u.nextId) &&
    openQty(u.orders) <= MAX_OPEN
  );
}
…
export function accepts(u: ChainUi, qty: int, price: int): boolean {
  return validQty(qty) && price > 0 && openQty(u.orders) + qty <= MAX_OPEN;
}

/** Place an order for a ticket if it is accepted; otherwise nothing changes. @opaque */
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  requires(validQty(qty));
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  // an accepted order is added exactly as the ticket says, under the next id ...
  ensures((r: ChainUi) => implies(accepts(u, qty, price), r.orders.some((o) => orderFor(o, u.nextId, t, qty, price))));
  // ... and nothing else changes: one order more (none for a rejected one), the others kept
  ensures((r: ChainUi) => r.orders.length === (accepts(u, qty, price) ? u.orders.length + 1 : u.orders.length));
  ensures((r: ChainUi) => keepsOrders(u, r) && keepsAllHolds(u, r) && sameView(u, r));
  // the limit depends on the current state, so it is checked here, not at the dispatch site
  if (!accepts(u, qty, price)) return u;
  …
```

Two design choices, both from the commit. The rule lives in one function, `accepts`: the guard
and both "an order is added" postconditions use it, so a new rule is added in one place. And the
limit is *not* part of `validAction`. It depends on the orders already working, that is, on the
state, and Step 9's precondition may mention only the action. So the quantity is checked where
the order is built, and the limit is checked in `place`, on the state the action is applied to.

One consequence of the first choice: `accepts` is part of the specification, not something it
checks. A stricter rule, such as `+ qty < MAX_OPEN`, changes the guard and the contract together
and still verifies (a [probe](options-chain/probes/53-rules-changed/) on snapshot 53, not one
of the steps, which also changes `levelsOf`, Step 18a); the invariant bounds the total only from
above. So `accepts` has to be right as
written, and the same holds for every function a contract calls by name. (Step 18 ties
`accepts` to the invariant, so that this change no longer verifies.)

### 10a. Sums need induction ([log](options-chain/29-open-cap-unproved.txt), [full log](options-chain/29-open-cap-unproved-full.txt), [snapshot](options-chain/steps/29-open-cap-unproved/src/))

This snapshot is the commit's `src/` with `proofs/model.lean` as it was before the commit: an
`import` and an `open`, no lemmas.

```
$ vreact verify
…
  INCOMPLETE         place
      ↳ an obligation of it failed
  INCOMPLETE         cancel
      ↳ an obligation of it failed
…
  INCOMPLETE         chainReducer
      ↳ it uses place, which is not verified: an obligation of it failed
…
  ✗ src/reducer.ts                           23/25
…
  ✗ src/OptionsChain.tsx                     36/37
…
Failed obligations
✗ src/OptionsChain.tsx:32:17  [init-invariant] OptionsChain: initial state satisfies the invariant
    │ …
    │ h : -1 * model.openQty [] + 1001 ≤ 0
    │ ⊢ False
✗ src/reducer.ts:181:11  [postcondition] postcondition of place: implies(wellFormed(u), wellFormed(r))
    │ …
    │ h : ((1 ≤ qty ∧ qty ≤ 500) ∧ 0 < price) ∧ model.openQty u.orders + qty ≤ 1000
    │ h_1 :
    │   -1 *
    │         model.openQty
    │           (u.orders ++
    │             [{ id := u.nextId, expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.ask,
    │                 qty := qty, price := price }]) +
    │       1001 ≤
    │     0
    │ …
    │ ⊢ False
✗ src/reducer.ts:198:11  [postcondition] postcondition of cancel: implies(wellFormed(u), wellFormed(r))
    │ …
    │ h₁₇ :
    │   (((1 ≤ u.heat ∧ u.heat ≤ 5) ∧ (List.map (fun o => o.id) u.orders).Nodup) ∧
    │       ∀ (x : model.Order), x ∈ u.orders → ((1 ≤ x.qty ∧ x.qty ≤ 500) ∧ 0 < x.price) ∧ x.id < u.nextId) ∧
    │     model.openQty u.orders ≤ 1000
    │ hsub : (List.map (fun o => o.id) (List.filter (fun x => !JS.eq x.id id') u.orders)).Nodup
    │ h : -1 * model.openQty (List.filter (fun x => !JS.eq x.id id') u.orders) + 1001 ≤ 0
    │ …
    │ ⊢ False

✗ NOT VERIFIED  139/142 obligations proved, 3 failed; components: 4/6 verified  (26.6s)
```

This time the hypotheses are not a counterexample. Each set contradicts itself, for anyone who
knows how a sum behaves:

* **The initial state.** `h` says that the total of no orders, `openQty []`, is at least 1001.
  It is 0.
* **`place`.** `h` is `accepts`: the old total plus `qty` is at most 1000. `h_1` says that the
  total of the old orders followed by the new one is at least 1001. Since
  `openQty(xs ++ [o]) = openQty(xs) + o.qty`, the two cannot both hold.
* **`cancel`.** `h₁₇` is the invariant before the cancel: every order has a quantity of at least
  1, and the total is at most 1000. `h` says that the total of the orders left after the
  `filter` is at least 1001. Removing orders whose quantities are positive cannot raise the
  total.

The automation knows none of these three facts. `openQty` is `@opaque`, so in the reducer and in
the chain it is just a name, with no contract. And the facts hold for lists of every length:
proving them takes induction over the list, which the automation does not do. Step 1d hit the
same limit and stated something weaker instead. Here nothing weaker will do: the invariant is
about the sum itself. The tool's documentation lists this case ("invariants about sums
(`reduce`) under filter/map: provable, but needs a Lean lemma in `proofs/`"). The code is right;
the proof needs help.

### 10b. A proof file ([log](options-chain/30-open-cap.txt), [snapshot](options-chain/steps/30-open-cap/src/), [proofs](options-chain/steps/30-open-cap/proofs/model.lean))

A **proof file** is a Lean file next to `src/`: `proofs/model.lean` holds **lemmas** (helper
theorems, proved once and then used by other proofs) about the Lean that vreact generates for
`src/model.ts` (`import VTS.model.Defs`; the function is
`VTS.model.openQty`, its body a `List.foldl`). vreact imports it into the generated Lean of every
module that imports `model.ts`. That is where the three goals are: in `reducer.ts` and in
`OptionsChain.tsx`. This is the walkthrough's first hand-written proof. Each `theorem` states a
fact; the lines after `by` are the tactics that prove it: `unfold` replaces a function by its
definition, `simp` and `rw` rewrite with known equations, `omega` settles linear integer
arithmetic, `cases` splits on the possible values of a term, and `induction … with` has one case
per shape of the list (empty, or an element followed by a list). You do not need to follow
every step: Lean's kernel checks them. The commit's file, in full:

```lean
import VTS.model.Defs
open VReact

@[vreact_simp] theorem openQty_nil : VTS.model.openQty [] = 0 := by
  unfold VTS.model.openQty
  rfl

theorem openQty_foldl_acc (os : List VTS.model.Order) (a : Int) :
    os.foldl (fun (n : Int) (o : VTS.model.Order) => (n + o.qty)) a
      = a + os.foldl (fun (n : Int) (o : VTS.model.Order) => (n + o.qty)) 0 := by
  induction os generalizing a with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons]
    rw [ih (a + o.qty), ih (0 + o.qty)]
    omega

/-- Peeling off the first order. No induction: lemma `openQty_foldl_acc` does the work. -/
@[vreact_simp] theorem openQty_cons (o : VTS.model.Order) (os : List VTS.model.Order) :
    VTS.model.openQty (o :: os) = o.qty + VTS.model.openQty os := by
  unfold VTS.model.openQty
  simp only [List.foldl_cons]
  -- ⊢ List.foldl … (0 + o.qty) os = o.qty + List.foldl … 0 os
  rw [openQty_foldl_acc os (0 + o.qty)]
  omega

/-- The total of two lists joined is the sum of their totals (`place` appends an order). -/
@[vreact_simp] theorem openQty_append (xs ys : List VTS.model.Order) :
    VTS.model.openQty (xs ++ ys) = VTS.model.openQty xs + VTS.model.openQty ys := by
  induction xs with
  | nil => simp [openQty_nil]
  | cons x xs ih =>
    -- ⊢ openQty (x :: xs ++ ys) = openQty (x :: xs) + openQty ys
    rw [List.cons_append, openQty_cons, openQty_cons, ih]
    -- ⊢ x.qty + (openQty xs + openQty ys) = x.qty + openQty xs + openQty ys
    omega

/-- Removing orders never raises the total, as long as no quantity is negative (`cancel`). -/
theorem openQty_filter_le (p : VTS.model.Order → Bool) (os : List VTS.model.Order)
    (h : ∀ o ∈ os, 0 ≤ o.qty) :
    VTS.model.openQty (os.filter p) ≤ VTS.model.openQty os := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have ho : 0 ≤ o.qty := h o (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    -- does the filter keep `o`?
    cases hp : p o
    · -- no:  openQty (filter p os) ≤ o.qty + openQty os
      simp [hp, openQty_cons]
      omega
    · -- yes: o.qty + openQty (filter p os) ≤ o.qty + openQty os
      simp [hp, openQty_cons]
      omega

-- Not a rewrite rule (an inequality with a side condition): let `grind` use it whenever it
-- sees the total of a filtered list; it proves the side condition from the invariant.
grind_pattern openQty_filter_le => VTS.model.openQty (List.filter p os)
```

How it fits together:

* **The induction.** `openQty` folds from 0, but after the first order the fold continues from
  `o.qty`, not from 0. So the useful fact is about every start value: folding from `a` gives
  `a` plus the fold from 0 (`openQty_foldl_acc`). Its proof is an induction over the list that
  *generalizes* `a`, because the start value changes at each step. With it, `openQty_cons` needs
  no induction of its own. `openQty_append` and `openQty_filter_le` are inductions over the
  list, each step using `openQty_cons`; in the filter proof, one case per answer of the filter
  for the first order.
* **`@[vreact_simp]`** adds an equation to the rewrite rules of `vreact_auto`, vreact's
  automation. It rewrites the left side into the right side wherever the left side appears in
  a goal. With `openQty_append`, `openQty_cons` and `openQty_nil`, the total in `place`'s goal,
  `openQty(u.orders ++ [o])`, becomes `openQty(u.orders)` plus the new order's quantity, and `h`
  and `h_1` are then plain arithmetic. `openQty_nil` alone settles the initial state.
* **`grind_pattern`** tells `grind` (the automation's main tactic, Step 1c) when to use a lemma
  that cannot be a rewrite rule. `openQty_filter_le` is an inequality, and it holds only under a
  side condition (no negative quantity). The pattern `VTS.model.openQty (List.filter p os)`
  means: whenever a term of that shape appears in a goal, add the lemma for that `p` and `os`.
  `cancel`'s goal has such a term, `grind` adds "the total after the filter is at most the total
  before, if no quantity is negative", and proves the side condition from the invariant (every
  working order has at least 1 lot).

Proof files are imported into the generated Lean, so whatever they declare is in force while
the app is checked. An `axiom` there could "prove" `False`, an `instance` could change what `===`
means for a record, and a macro could change how the generated code reads. That is why vreact
applies **the proof-file whitelist**. Before Lean runs, it parses every proof file with Lean's
own parser and accepts only `import`s of the generated modules (`VTS.…`), of other proof files,
of the whole library and of `Init`; the declarations `theorem`, `def`, `abbrev` and `example`;
`open`, `namespace`/`section`/`end`, `variable`, `universe`, `include`/`omit`, module docs
(`/-! … -/`), `#check` and `#print`; the attributes `simp`, `vreact_simp` and `grind`, and
`grind_pattern`; and a few options (heartbeat, recursion and instance-search limits,
auto-bound implicits, diagnostics, linters, printing, traces). The exact rules, also for what
may appear inside a proof, are in the skill's `reference/obligations.md`. Everything else is
rejected with file, line and reason: `axiom`, `instance`, `macro`, `syntax`, `#eval`, other
attributes and options. For
example, a proof file with
`axiom openQty_le_cap (os : List VTS.model.Order) : VTS.model.openQty os ≤ 1000` in place of
the lemmas ([probe](options-chain/probes/30-axiom-in-proof-file/), not one of the steps) stops
the run before Lean starts: "is not allowed in a proof file: an axiom is an unproved
assumption: state it as a theorem and prove it (assumptions belong in the source, as
`assume(…)` or `@trusted`, where the report shows them)". A lemma left as
`sorry` is accepted, but `sorryAx` then appears in the axioms of everything that uses it
(INCOMPLETE). After the build, Lean's kernel checks every declaration of the generated modules
and of the proof files again, in a fresh process. So a proof file can add facts, but only proved
ones. (The whitelist came to vreact after this commit; the file passes it unchanged.)

```
$ vreact verify
…
  VERIFIED           openQty
…
  VERIFIED           accepts
  VERIFIED           place
  VERIFIED           cancel
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
…
✔ VERIFIED  142/142 obligations proved; components: 6/6 verified  (24.9s)
```

The count is the same as at step 29: lemmas are not obligations. Lean checks them while it
builds the project, and the certificate's axioms are still the three standard ones, because
the lemmas are proved, not assumed. The report does not list the lemmas themselves. A lemma
whose proof fails does show: in a [probe](options-chain/probes/30-failing-lemma/) (not one of
the steps) that dropped the last `omega` of `openQty_cons`, the report listed the Lean error
under "Errors in user proofs (proofs/*.lean)", and every obligation that Lean checks after the
proof file as not checked (137 of 142; NOT VERIFIED).

---

## Step 11: a Rally button

Then a Rally button: while it is on, the futures also climb one tick every
0.2 s, up to the top of the ±40-tick band (`MAX_MOVE`).

### 11a. A limit checked on the snapshot ([log](options-chain/31-rally-snapshot-bug.txt), [full log](options-chain/31-rally-snapshot-bug-full.txt), [snapshot](options-chain/steps/31-rally-snapshot-bug/src/App.tsx))

A first draft keeps the climb inside the band by not registering the interval at the top. The
effect re-runs whenever the feed changes, so the check looks fresh:

```tsx
const [rally, setRally] = useState<boolean>(false);
…
useEffect(() => {
  if (!rally || feed.offset >= MAX_MOVE) return;
  const id = setInterval(() => setFeed((f) => ({ ...f, offset: f.offset + 1 })), 200);
  return () => clearInterval(id);
}, [rally, feed]);
…
<button onClick={() => setRally(!rally)}>{rally ? "Stop rally" : "Rally"}</button>
```

```
$ vreact verify
…
  INCOMPLETE         App                    src/App.tsx:115
      ↳ an obligation of it failed
…
  ✗ src/App.tsx                              14/15

Failed obligations
✗ src/App.tsx:129:3  [effect-robust] timer callbacks of the effect preserve the invariant of App from any state
    │ `grind` failed
    │ …
    │ h : …  (a long hypothesis, 10 lines: --full shows it)
    │ s : State
    │ left : -1 * s.feed.offset + -40 ≤ 0
    │ left_1 : s.feed.offset + -40 ≤ 0
    │ …
    │ h_4 : -1 * (List.foldl (fun s u => u s) s (t e).updates).feed.offset + 41 ≤ 0
    │ h_5 : σ.rally = true
    │ h_6 : ¬-1 * σ.feed.offset + 40 ≤ 0
    │ ⊢ False

✗ NOT VERIFIED  144/145 obligations proved, 1 failed; components: 5/6 verified  (26.2s)

$ vreact verify --full     # the same failure, `h` whole (excerpt, lines 93-102 of the log)
    │ h :
    │   t = fun x =>
    │     if σ.rally = true then
    │       if 40 ≤ σ.feed.offset then { }
    │       else
    │         {
    │           updates :=
    │             [fun τ =>
    │               { feed := { offset := τ.feed.offset + 1, seed := τ.feed.seed }, paused := τ.paused, rally := τ.rally }] }
    │     else { }
```

The same pattern as Step 6. `h`, folded in the short report, is the timer callback `t`: if the
rally is on and the *snapshot* `σ` is below 40, it queues one update,
`offset := τ.feed.offset + 1`, applied to whatever state `τ` React holds when it runs. `s` is
that state: any state with a valid feed (`left`, `left_1`: −40 ≤ offset ≤ 40). `h_6` says the
snapshot was below 40, and `h_4` that the offset after the update is at least 41. A
counterexample: the snapshot shows 39, but by the time the timer fires, the random walk (or an
earlier rally tick) has moved the feed to 40, and 40 + 1 = 41. This is Step 6's stale closure
again. React runs the effect's cleanup only after the next render, so a tick of the old interval
can fire after the state has changed, and the update must keep the invariant from every valid
state, however unlikely. The commit message records the same finding: "vreact rejected that
version with an effect-robust failure (offset 40 + 1 = 41)".

### 11b. The limit inside the update ([log](options-chain/32-rally.txt), [snapshot](options-chain/steps/32-rally/src/App.tsx))

The fix checks the limit inside the functional update, on the state it is applied to. The check
before `setInterval` stays: it only saves an interval at the top of the band.

```tsx
const id = setInterval(() => setFeed((f) => (f.offset < MAX_MOVE ? { ...f, offset: f.offset + 1 } : f)), 200);
```

```
$ vreact verify
…
  ✓ src/App.tsx                              15/15

✔ VERIFIED  145/145 obligations proved; components: 6/6 verified  (25.0s)
```

Three obligations more, all in the App: two for the new effect (the effect itself and its timer
callback, each from any valid state) and one for the Rally button, which is checked as
rebase-safe like the Pause button (Step 6). In the browser, the commit message reports, the
rally climbs to +40 and stays there.

---

## Step 12: the rules of the feed, in one reducer

Snapshot 32 verifies, and yet the next commit's message reports a bug seen in the browser: Pause
at +7, then Rally, and the futures reached +21 within 3 seconds. The rally's interval never
looks at `paused`. Nothing in the spec said what Pause means: App's invariant says only that the
feed is valid, and a feed that moves while paused is valid. Like the surviving mutants of Step
7, this is a gap in the spec, not in the proofs.

The fix first writes down what Pause means. The feed, `paused` and
`rally` become one record, `Sim`, managed by a reducer, so every change to them goes through
one function, and that function's postconditions are the rules
([snapshot](options-chain/steps/34-sim-reducer/src/App.tsx)):

```ts
/** The simulation: the feed, and the two controls that drive it. One record, one reducer. */
export type Sim = { readonly feed: Feed; readonly paused: boolean; readonly rally: boolean };

export type SimAction =
  | { readonly kind: "tick" } // the 0.8 s random walk
  | { readonly kind: "rallyTick" } // the 0.2 s climb
  | { readonly kind: "togglePause" }
  | { readonly kind: "toggleRally" };
…
/** Every change to the simulation goes through here, so its contract holds for every update. */
export function simReducer(s: Sim, a: SimAction): Sim {
  ensures((r: Sim) => implies(validFeed(s.feed), validFeed(r.feed)));
  // while paused, nothing moves the feed
  ensures((r: Sim) => implies(s.paused, sameFeed(r.feed, s.feed)));
  // ... and while running, a tick is one step of the random walk (so "never move" is not a fix)
  ensures((r: Sim) => implies(!s.paused && a.kind === "tick", sameFeed(r.feed, stepFeed(s.feed))));
  …
}

export function App() {
  const [sim, dispatch] = useReducer(simReducer, { feed: { offset: 0, seed: 1 }, paused: false, rally: false });
  invariant(validFeed(sim.feed));
  // every 0.8 s the futures move by -2..+2 ticks
  useEffect(() => {
    if (sim.paused) return;
    const id = setInterval(() => dispatch({ kind: "tick" }), 800);
    return () => clearInterval(id);
  }, [sim.paused]);
  // rally: the futures also climb one tick every 0.2 s, up to the top of the band (no interval
  // while paused; simReducer ignores a late tick anyway)
  useEffect(() => {
    if (!sim.rally || sim.paused || sim.feed.offset >= MAX_MOVE) return;
    const id = setInterval(() => dispatch({ kind: "rallyTick" }), 200);
    return () => clearInterval(id);
  }, [sim.rally, sim.paused, sim.feed.offset]);
```

(`sameFeed(a, b)` compares the two fields of a feed.) The third postcondition matters: without
it, a reducer that ignores ticks would satisfy the spec. But it ties a tick to one step of
`stepFeed`, and `stepFeed`'s own contract says only that the feed stays valid. So it rules out
a reducer that skips the random walk, not a random walk that never moves: like `accepts` in
Step 10, `stepFeed` is part of the specification, and the comment's "never move" is about the
reducer alone. (A [probe](options-chain/probes/53-walk-frozen/) on snapshot 53, not one of the
steps: a `stepFeed` that always keeps the offset verifies. Step 18 gives `stepFeed` a contract
that rules this out, and rewords the comment.)

### 12a. A reducer that does what the old code did ([log](options-chain/33-sim-paused-bug.txt), [full log](options-chain/33-sim-paused-bug-full.txt), [snapshot](options-chain/steps/33-sim-paused-bug/src/App.tsx))

The obvious first version of the reducer just applies the moves, as the step-32 code did, and
leaves pausing to the effects, which stop their intervals while paused:

```ts
  // the effects stop their intervals while paused, so the reducer only applies the moves
  // (as the previous code did)
  switch (a.kind) {
    case "tick":
      return { ...s, feed: stepFeed(s.feed) };
    case "rallyTick":
      return s.feed.offset >= MAX_MOVE ? s : { ...s, feed: { ...s.feed, offset: s.feed.offset + 1 } };
    …
```

```
$ vreact verify
…
  INCOMPLETE         simReducer
      ↳ an obligation of it failed
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
…
  ✗ src/App.tsx                              17/18

Failed obligations
✗ src/App.tsx:133:11  [postcondition] postcondition of simReducer: implies(s.paused, sameFeed(r.feed, s.feed))
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
    │   … (the goal as stated: --full shows it)
    │ The goal splits into 13 cases. A case's name lists the branches that lead to it, outermost first: … Each case alone, smallest first, with up to 100000 heartbeats: 0 proved, 0 did not finish, then case h_2.isFalse failed (12 not tried):
    │ `grind` failed
    │ case grind.1.1.2.2
    │   … (2 earlier hypotheses: s, h₁₀: --full shows them)
    │ hcontract, hcontract_1, hcontract_2 : …  (3 contract instances, 118 lines: --full shows them)
    │ h : ¬40 ≤ s.feed.offset
…
    │ ⊢ False

✗ NOT VERIFIED  147/148 obligations proved, 1 failed; components: 6/6 verified  (64.6s)
```

Three things to note here.

**A timeout, then the case that fails.** The first line says the automation used up its budget
(Lean counts work in "heartbeats"; each obligation gets 1,000,000) without finishing. The claim
is false, but the automation searches for a proof, not for a counterexample, and here the search
does not end in time. After a timeout, vreact looks for the part that fails, as a diagnosis. The
goal splits into **cases**, one for each path through the `switch` and the conditions in the
reducer (and a few from the translation, such as the sign tests of `%` in the random walk).
vreact tries them one at a time, smallest first, each with a tenth of the budget and with half
of it in all, and stops at the first that fails, or when that half is used up. Here that is
the first one it tries, case `h_2.isFalse`. The name lists the branches, outermost first: `h_2`
is the second alternative of the `switch`, `"rallyTick"`, and `isFalse` is the false branch of
its condition `s.feed.offset >= MAX_MOVE`. The case's
hypotheses are a counterexample: `h₁₀` the feed is paused, `h` the offset is below 40
(`MAX_MOVE`). The short report leaves `h₁₀` out, as one of the two hypotheses farthest from the
conclusion, and names it on its first line; `--full` prints it, `h₁₀ : s.paused = true`
([full log](options-chain/33-sim-paused-bug-full.txt)). In that state a rally tick moves the
feed one tick up, while paused. (The line `case grind.1.1.2.2` above them is `grind`'s own name
for the branch of its search where it stopped; it can be ignored.)

The diagnosis stops at the first case that fails ("12 not tried"), so it does not say whether
other cases fail too. The `"tick"` case does, and it is also where the budget goes: it has to
decide whether one step of the random walk can leave a paused feed unchanged, a question about
`(seed * 75 + 74) % 65537`. Two probes, not steps, show it. Each puts one case of the draft
back into the commit's reducer of step 34, not into snapshot 33, so the goal is not split the
same way: 12 cases instead of 13. With only the `"tick"` case wrong
([probe](options-chain/probes/33-tick-case-only/)), the obligation times out again. The
diagnosis proves 3 of the 12 cases, does not finish 5, does not try the last 4 (five unfinished
cases of a tenth each use up the half), and shows the first unfinished one, a case of the
`"tick"` alternative (`h_1`). With only the `"rallyTick"` case wrong
([probe](options-chain/probes/33-rally-case-only/)), `grind` fails without a timeout, with the
same counterexample as above. So Part 1's lesson applies again, and the
report helps with it: when an obligation is not proved, look for a counterexample before
blaming the automation. The commit message names two ways the feed moved while paused: the
rally interval never checked `paused` (the bug seen in the browser), and a random-walk tick
dispatched just before Pause can be applied after it. The second needs a correction. React
applies a hook's queued actions in the order they were dispatched (`vreact/docs/SEMANTICS.md`
§2.2), so a tick dispatched before Pause is applied before it, to a running feed, and moves it:
no reducer can refuse that tick. React may render the Pause first and the tick after it, so the
futures can still move once on screen after the click ("Not proven here" lists this). What the
`"rallyTick"` case of snapshot 33 shows is different: a rally tick applied to a paused state,
that is, a tick dispatched after Pause. The model allows that: it has no cleanup step, so a
timer it registers may fire against any later state (SEMANTICS §2.6). And from 12c on, the
clocks never stop, so every tick after Pause meets a paused state.

**Contract instances, collapsed.** As in Step 3, the `hcontract…` hypotheses are facts from
contracts: what the `ensures` of the functions in the goal say about these arguments. Here they
are long formulas, mostly about the random walk's arithmetic, so the short report folds them
into one line that names and counts them, and the short hypotheses after them stay in view.
`--full` prints them.

**The effects do not help.** In this snapshot both effects stop their intervals while paused,
and still the postcondition fails. A reducer's postcondition is about the reducer alone, for
every state and every action. That is the point. The code that dispatches a tick cannot know
the state the tick will be applied to: in the model a timer may fire after Pause, and in 12c
the clocks tick whatever the state. So only the reducer, looking at the state the action is
applied to, can enforce "paused means frozen" for every action. This is a **reducer that owns
the rules**: the rules are checked in the reducer, on the state each action meets, and stated as
its contract. Code that dispatches can only ask.

As in Step 7a, the certificate is VERIFIED while the verdict is NOT VERIFIED: App's invariant,
`validFeed(sim.feed)`, needs only `simReducer`'s first postcondition, which holds. "Paused means
frozen" is a functional property, reported as failed (`simReducer` INCOMPLETE, `App.tsx`
17/18). Read the verdict line, not only the certificate.

### 12b. The rules in the reducer ([log](options-chain/34-sim-reducer.txt), [snapshot](options-chain/steps/34-sim-reducer/src/App.tsx))

The commit's reducer checks `paused` on the state each tick is applied to:

```ts
  // `paused` is checked here, on the state the action is applied to: a tick dispatched just
  // before the pause can still arrive after it, and the rally has its own interval
  switch (a.kind) {
    case "tick":
      return s.paused ? s : { ...s, feed: stepFeed(s.feed) };
    case "rallyTick":
      return s.paused || s.feed.offset >= MAX_MOVE ? s : { ...s, feed: { ...s.feed, offset: s.feed.offset + 1 } };
    case "togglePause":
      return { ...s, paused: !s.paused };
    case "toggleRally":
      return { ...s, rally: !s.rally };
  }
```

```
$ vreact verify
…
  VERIFIED           sameFeed
  VERIFIED           simReducer
…
  ✓ src/App.tsx                              18/18

✔ VERIFIED  148/148 obligations proved; components: 6/6 verified  (28.6s)
```

The three new obligations are `simReducer`'s three postconditions. `simReducer` has no
`requires`, so its `dispatch` calls add no precondition obligations. In the browser (again
from the commit message), a rally while paused leaves the feed unchanged, and the feed moves
again after Resume. The code comment repeats the commit message's "dispatched just before the
pause"; as 12a explains, what the check refuses is a tick dispatched after it.

### 12c. Clocks that only say "time passed" ([log](options-chain/35-sim-clocks-bug.txt), [full log](options-chain/35-sim-clocks-bug-full.txt), [log](options-chain/36-sim-clocks.txt), [snapshot](options-chain/steps/36-sim-clocks/src/App.tsx))

Once the reducer owns the rules, the effects need none. The last commit of this series makes
both intervals **clocks that only say "time passed"**: registered once for the app's lifetime
(`[]` deps), each dispatches a bare tick, and the reducer decides on the state each tick meets
whether it moves the feed. The 200 ms interval is no longer torn down and set up again after
every move, no timer reads a snapshot, and the rules are proved in one place:

```ts
  // a rally tick moves the feed only while a rally is on ...
  ensures((r: Sim) => implies(a.kind === "rallyTick" && !s.rally, sameFeed(r.feed, s.feed)));
  // ... and then it climbs one tick, up to the top of the band
  ensures((r: Sim) =>
    implies(a.kind === "rallyTick" && s.rally && !s.paused && s.feed.offset < MAX_MOVE, r.feed.offset === s.feed.offset + 1),
  );
  // The rules live only here, checked on the state the action is applied to: App's intervals
  // tick unconditionally, and a tick may arrive after a pause or after the rally is stopped.
  …
  // Two clocks for the whole lifetime of the app. They only say "time passed": whether a tick
  // moves the feed (paused? rally on? at the top of the band?) is decided, and proved, in
  // simReducer. A tick that changes nothing returns the same state, so React skips the update.
  useEffect(() => {
    const id = setInterval(() => dispatch({ kind: "tick" }), 800);
    return () => clearInterval(id);
  }, []);
  useEffect(() => {
    const id = setInterval(() => dispatch({ kind: "rallyTick" }), 200);
    return () => clearInterval(id);
  }, []);
```

The `"rallyTick"` case of step 34 has no reason to look at `rally`: its interval ran only while
the rally was on. Keep that case with the new clocks
([snapshot](options-chain/steps/35-sim-clocks-bug/src/App.tsx)), and every 0.2 s a rally tick
arrives whether or not Rally is on: the futures would climb to the top of the band in about 8
seconds after loading. The new postcondition catches it:

```
$ vreact verify
…
  ✗ src/App.tsx                              19/20

Failed obligations
✗ src/App.tsx:137:11  [postcondition] postcondition of simReducer: implies(a.kind === "rallyTick" && !s.rally, sameFeed(r.feed, s.feed))
    │ `grind` failed
    │ case grind.1.1.2.2
    │ s : Sim
    │ hcontract, hcontract_1, hcontract_2, hcontract_3 : …  (4 contract instances, 125 lines: --full shows them)
    │ h₁₆ : ¬s.rally = true
    │ h : ¬s.paused = true
    │ h_1 : ¬40 ≤ s.feed.offset
…
    │ ⊢ False

✗ NOT VERIFIED  149/150 obligations proved, 1 failed; components: 6/6 verified  (32.4s)

$ vreact verify --full     # the same failure, complete goal (excerpt, lines 206-209 of the log)
    │ hcontract_3 :
    │   s.paused = true →
    │     (if s.paused = true then s.feed.offset else if 40 ≤ s.feed.offset then s.feed.offset else s.feed.offset + 1) =
    │       s.feed.offset
```

As in 12a, the contract instances are collapsed into one line, and the counterexample follows
it: `h₁₆` the rally is off, `h` the feed is running, `h_1` the offset is below 40. In that state
a rally tick moves the feed. The full goal has the four instances in 125 lines; one of them,
`hcontract_3`, shows in passing what this reducer returns for a rally tick: the offset `+ 1` in
exactly that situation. The fix is the commit's `!s.rally ||`
([log](options-chain/36-sim-clocks.txt)):

```ts
    case "rallyTick":
      return !s.rally || s.paused || s.feed.offset >= MAX_MOVE ? s : { ...s, feed: { ...s.feed, offset: s.feed.offset + 1 } };
```

```
$ vreact verify
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           25/25
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     37/37
  ✓ src/App.tsx                              20/20

✔ VERIFIED  150/150 obligations proved; components: 6/6 verified  (31.3s)
```

The two new obligations are the two new postconditions. At step 36 the app has 6 components,
54 functions and 150 obligations, a proof file with five lemmas, and a certificate on the three
standard axioms.

---

## Step 13: the state on Maps and Sets

The UI state of step 36 still uses arrays for three things that are not lists:

* `collapsed: readonly int[]`, the collapsed expiries, is a **set**: order and duplicates mean
  nothing, and `sameView` had to compare it "as a set" with two `every … includes`;
* `held: readonly Hold[]`, a list of `{ expiry, price }`, is a **map** from an expiry to a
  price: `heldPrice` reads the *first* hold of an expiry, so `holdAt` had to put the new hold
  first and filter out the old one;
* `orders: readonly Order[]` is a **map** from an id to an order: the invariant had to say
  `distinct(u.orders, (o) => o.id)`, and the frame `keepsOrders` searched the new list for
  every old order (a nested `some` over seven fields).

This step moves the state onto `ReadonlySet` and `ReadonlyMap`, and Step 14 extracts the
comparisons into generic helpers, proved once for every key type they allow. The components
change only where they read the state (`has`, `get`, `size`). Then two features use the new
structures (watched strikes, Step 15; amending an order, Step 16), a second mutation audit
checks the new frames (Step 17), an outside review checks the whole spec (Step 18), and Step 19
is the final app.

**Maps and Sets in VTS.** `ReadonlyMap<K, V>` and `ReadonlySet<T>` (and `Map`, `Set`) may
appear wherever a type may: parameters, results, state, props, record fields. Keys and Set
elements are `int`, `string`, `boolean` or a string-literal enum: JS Maps compare keys with
SameValueZero, which for these types is plain equality. (`number` keys are rejected because of
`NaN` and `-0`; records and arrays because JS compares them by identity, so a copy is never
found.) In Lean a Map is its list of entries, **in insertion order**, with distinct keys, as in
JS: `set` on a present key keeps its position, on a new key appends it. The reads are `get`
(`undefined` for a missing key), `has` and `size`. Iteration is allowed where it is consumed at
once (`[...m]`, `[...m.keys()]`, `for…of`, `Array.from`), because a JS iterator is used up once
and sees later changes. There are two ways to update:

* in an expression, a **pure update** of a fresh copy: `new Map(m).set(k, v)`,
  `new Set(s).add(x)`;
* in statements, **copy, then mutate**: `const n = new Map(m); n.delete(k); return n;`. Only a
  `const` initialised with `new Map(…)`/`new Set(…)` in the same function may be mutated, and
  only while nothing else can see it.

The new state ([snapshot](options-chain/steps/41-reducer-maps-verified/src/reducer.ts)):

```ts
export type ChainUi = {
  readonly collapsed: ReadonlySet<int>; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly held: ReadonlyMap<int, int>; // unlocked expiry → the price its window is held at
  readonly focus: int | null; // the expiry last jumped to
  readonly heat: int; // heat-map threshold, in ticks
  readonly orders: ReadonlyMap<int, Order>; // working orders by id, in the order they were placed
  readonly nextId: int; // the id of the next order: above every id in use
};
```

(The first draft leaves `nextId` out; Step 13d shows why it is back.)

The `Readonly` forms go into the state on purpose: TypeScript then refuses `set`, `add` and
`delete` on them (Step 13a shows why that matters).

**`Order` loses its `id`.** The orders are now a Map from id to order, so the id is the key.
Keeping an `id` field as well would store it twice, and then the invariant must tie the two
together (`[...u.orders].every(([k, o]) => o.id === k)`), or a list rendered from
`[...ui.orders.values()]` with `key={o.id}` has no reason to have distinct keys. Without the
field there is one source of truth: the working orders are rendered from the entries, keyed by
the Map key, whose keys are distinct by construction
([snapshot](options-chain/steps/41-reducer-maps-verified/src/OptionsChain.tsx)):

```tsx
{[...ui.orders].map(([id, o]) => (
  <li key={id}>
    …
    <button onClick={() => dispatch({ kind: "cancel", id: id })}>Cancel</button>
  </li>
))}
```

The cost is small: code that needs an order's id gets it next to the order, from the entry.
`distinct(u.orders, (o) => o.id)` disappears from the invariant.

At first `proofs/model.lean` stays as it was: `openQty` still sums a list, and the reducer
passes it `[...u.orders.values()]`. Step 13d shows why that is not enough.

### 13a. Two rejections ([log](options-chain/37-sets-maps-rejected.txt), [snapshot](options-chain/steps/37-sets-maps-rejected/src/))

The first draft changes the types, ports the operations, and makes the mechanical edits in the
components in the same snapshot: `vreact verify` checks the whole app, so a state type cannot
change in `reducer.ts` alone. In `OptionsChain.tsx`, `includes` becomes `has`, `heldPrice(…)`
becomes `get`, `ui.orders.length` becomes `ui.orders.size`, and the orders list is rendered from
the entries as above. Two places in the draft are wrong. `toggle` mutates the state's Set (in
this draft the field is typed `Set<int>`, so that `add` and `delete` compile):

```ts
export function toggle(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.collapsed.has(id) === !u.collapsed.has(id));
  if (u.collapsed.has(id)) u.collapsed.delete(id);
  else u.collapsed.add(id);
  return { ...u };
}
```

and the chain reads a hold with `get` and keeps the old null test in the lock button's handler:

```tsx
const held = ui.held.get(e.id);
const center: int | null = held ?? live;
…
<TermRow
  expiry={e}
  open={open}
  held={held ?? null}
  focused={ui.focus === e.id}
  onToggle={() => dispatch({ kind: "toggle", expiry: e.id })}
  onLock={() => {
    if (held !== null) dispatch({ kind: "follow", expiry: e.id });
    else if (live !== null) dispatch({ kind: "hold", expiry: e.id, price: live });
  }}
  …
```

TypeScript accepts both. `vreact verify` stops before Lean, with two rejections, one in each
file:

```
$ vreact verify
✗ VTS src/reducer.ts:85:28: u.collapsed.delete(…) mutates u.collapsed, which is not a local variable of this function (a parameter, prop, state value, constant, or a value read from one: the caller, React or other code holds the same object, and would see the change); mutate a fresh copy instead: const next = new Set(u.collapsed); next.delete(…);
✗ VTS src/OptionsChain.tsx:119:23: `held` can be undefined but never null (optional fields, find(), at(), a Map's get() and ?. give undefined), so `!== null` is always true in JS: write !== undefined or != null
```

**The mutation is a real React bug.** `toggle` returns a new `ChainUi` object, but its
`collapsed` is the *same* Set as the old state's, and that Set has changed. The app's
`main.tsx` renders `<StrictMode>`. In development, StrictMode calls every reducer twice with
the same state and action, to find impure reducers. The first call adds the expiry to the Set,
the second sees it there and deletes it again: the ▸/▾ button does nothing at all. In a
production build the button works, but the state React keeps as "previous" has changed too:
everything that compares the old and the new `ui.collapsed` (an effect or a memo that depends on
it, a memoized child) sees one and the same Set and does not update, and when React applies
queued actions again to an older state (rebasing, Part 1, Step 6), that older state is no longer
what it was. The Lean model has no shared objects at all: a Map or a Set is a value. So VTS
accepts a mutation only where the two meanings agree, on a fresh local copy that nothing else
can see yet.

With the field typed `ReadonlySet<int>` (as the final state has it), the same `toggle` does not
even compile. `vreact verify` then reports TypeScript's errors instead (a
[probe](options-chain/probes/37-readonly-set/): this snapshot with that one type changed, not
one of the steps): `error TS2339: Property 'delete' does not exist on type
'ReadonlySet<number>'`, and the same for `add`.

Both checks find the same bug. VTS's applies to every Map or Set, also to one that reaches a
function typed as a mutable `Map` or `Set`, and its message says what to do instead. The fix
copies first ([snapshot](options-chain/steps/38-reducer-synth-maps/src/reducer.ts)):

```ts
const collapsed = new Set(u.collapsed);
if (collapsed.has(id)) collapsed.delete(id);
else collapsed.add(id);
return { ...u, collapsed: collapsed };
```

**`get` gives `undefined`, never `null`.** `ui.held.get(e.id)` is `int | undefined`. TypeScript
flagged the two places where that type did not fit (`center` and the `held` prop), and the
draft fixed those with `??`. It did not flag `held !== null`: comparing anything with `null` is
legal TypeScript. In JS the test is always true, so the lock button would always dispatch
`follow`, also for an expiry that is not held, and an expiry could never be unlocked. The
display uses `held ?? null` and shows "live" correctly, so the bug would be easy to miss. The fix
converts once, where the value is read, and the rest of the code stays as it was in Part 1
([snapshot](options-chain/steps/41-reducer-maps-verified/src/OptionsChain.tsx)):

```tsx
const held = ui.held.get(e.id) ?? null;
const center: int | null = held === null ? live : held;
```

Lesson: when a type changes, TypeScript reports the places where the new type does not fit.
A test that compiles for any type, such as `!== null`, keeps compiling and changes its meaning.

### 13b. Synth: "not held" is satisfied by holding nothing ([log](options-chain/38-reducer-synth-maps.txt), [snapshot](options-chain/steps/38-reducer-synth-maps/src/reducer.ts))

The draft writes the contracts of the operations on holds and orders in the Map's own
vocabulary, `get` and `has`. `holdAt` is written by hand (`new Map(u.held).set(id, price)` is the
obvious pure update). The two deletions, `follow` and `cancel`, are left as holes for synth, as
in Part 1, Step 2:

```ts
export function follow(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.held.has(id));
  ensures((r: ChainUi) => sameView(u, r));
  return hole<ChainUi>();
}
…
export function cancel(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.orders.has(id));
  return hole<ChainUi>();
}
```

```
$ vreact synth src/reducer.ts
hole in follow: ChainUi   scope: u, u.collapsed, u.filter, u.held, u.focus, u.heat, u.orders, id
  candidate passes 400 random tests: { ...u, held: new Map() }   (27 candidate(s) tested in 0.2s)
  ✔ proved by Lean: { ...u, held: new Map() }
hole in cancel: ChainUi   scope: u, u.collapsed, u.filter, u.held, u.focus, u.heat, u.orders, id
  candidate passes 400 random tests: { ...u, orders: new Map() }   (36 candidate(s) tested in 0.2s)
  ✔ proved by Lean: { ...u, orders: new Map() }
(src/reducer.ts not modified: rerun with --write to keep the proved fill(s))
```

Both fills are proved, and both are wrong: `follow` unlocks *every* expiry, `cancel` cancels
*every* order. "The key is absent" is satisfied by the empty Map. The contracts lack the frame
conditions (Part 1, Step 2a), now for the entries of a Map
([snapshot](options-chain/steps/39-reducer-synth-frames/src/reducer.ts)):

```ts
/**
 * Frame condition: the holds of the expiries other than `id` are unchanged: none dropped, none
 * added, none moved to another price.
 */
export function keepsHolds(u: ChainUi, r: ChainUi, id: int): boolean {
  return (
    [...u.held].every(([x, p]) => x === id || r.held.get(x) === p) &&
    [...r.held].every(([x, p]) => x === id || u.held.get(x) === p)
  );
}
…
/** Frame condition: the working orders other than `id` are unchanged: none dropped, none added. */
export function keepsOrdersExcept(u: ChainUi, r: ChainUi, id: int): boolean {
  return (
    [...u.orders].every(([k, o]) => k === id || sameOrder(o, r.orders.get(k))) &&
    [...r.orders].every(([k, o]) => k === id || sameOrder(o, u.orders.get(k)))
  );
}
```

`([x, p]) => …` destructures an entry `[key, value]` by position, as in JS. `sameOrder(o, p)`
compares the six fields of two orders (`p` is `Order | undefined`: a missing order is not the
same order). Part 1's `keepsHolds` said only "every old hold of another expiry is still
there"; it let an operation *add* holds to other expiries. With a Map the other direction is
one more `every`, so the frame now says "unchanged" both ways. `holdAt` and `follow` get
`sameView(u, r) && keepsHolds(u, r, id)`, `cancel` gets
`keepsOrdersExcept(u, r, id) && keepsAllHolds(u, r) && sameView(u, r)`.

### 13c. Synth with the frames, and a weak contract it finds on the way ([log](options-chain/39-reducer-synth-frames.txt), [snapshot](options-chain/steps/39-reducer-synth-frames/src/reducer.ts))

```
$ vreact synth src/reducer.ts
hole in follow: ChainUi   scope: u, u.collapsed, u.filter, u.held, u.focus, u.heat, u.orders, id
  candidate passes 400 random tests: { ...jump(u, id), collapsed: u.collapsed, focus: u.focus }   (11503 candidate(s) tested in 47.1s)
  ✗ Lean rejects { ...jump(u, id), collapsed: u.collapsed, focus: u.focus }: postcondition of follow: sameView(u, r) && keepsHolds(u, r, id) (src/reducer.ts:145:11)
  14612 candidates tested in 60.0s, up to size 7; stopped: the 60s time limit was reached at size 7
  no verified solution for hole in follow: 1 candidate(s) passed the tests, none was proved
  the random tests accept candidates that Lean rejects: write this one by hand
hole in cancel: ChainUi   scope: u, u.collapsed, u.filter, u.held, u.focus, u.heat, u.orders, id
  14661 candidates tested in 60.0s, up to size 7; stopped: the 60s time limit was reached at size 7
  no verified solution for hole in cancel: no candidate passed the tests
  most common failure (14661×): u: postcondition fails on [{"collapsed":{"Set":[1,0,3]},"filter":"s3","held":{"Map":[]},…},5] ↦ …
  write this one by hand (synth builds straight-line expressions; guarded updates need an `if`; it only adds to a Map or Set, by new Map(m).set(k, v) or new Set(s).add(x): deleting is not in its grammar), or check that the spec is satisfiable
```

(The `most common failure` line is shortened here. In the log it prints the whole random state:
Maps and Sets appear as `{"Map":[[key, value], …]}` and `{"Set":[…]}`, with two working
orders, one of them under the id `5` that `cancel` was asked to remove. Synth's random inputs
are seeded (Step 1b), so a re-run prints the same state.)

The empty Maps are gone: the frames refute them. Two other things are visible.

**Synth found a weak contract in `jump`.** For `follow` synth proposes "jump to the expiry,
then put back the collapsed expiries and the focus". In JavaScript that is exactly `follow`:
`jump` deletes the expiry's hold and nothing else in `held`, so the candidate passes all 400
random tests. Lean rejects it anyway, and the reason is not in `follow`: `jump` is `@opaque`,
so its callers know only its contract, and that says
`!r.collapsed.has(id) && !r.held.has(id) && r.focus === id`, nothing about the holds of the other
expiries. A `jump` that dropped every hold would satisfy it. That is the missing frame of `jump`
on Part 1's list (Step 8); Step 14 adds it, with the other missing frames.
Lesson: when the tests accept a candidate and Lean rejects it, look at the contracts of the
functions the candidate calls.

**Synth cannot delete.** Its closing hint for `cancel` says so. Its candidates are expressions,
and its expressions for Maps and Sets only add (`new Map(m).set(k, v)`, `new Set(s).add(x)`).
JS's `m.delete(k)` returns a boolean, not the Map, so a deletion is a statement on a fresh copy.
(An expression that deletes exists, `new Map([...m].filter(([k]) => k !== id))`, but synth does
not generate it.) The two operations are written by hand
([snapshot](options-chain/steps/41-reducer-maps-verified/src/reducer.ts)):

```ts
export function follow(u: ChainUi, id: int): ChainUi {
  …
  const held = new Map(u.held);
  held.delete(id);
  return { ...u, held: held };
}
…
export function cancel(u: ChainUi, id: int): ChainUi {
  …
  const orders = new Map(u.orders);
  orders.delete(id);
  return { ...u, orders: orders };
}
```

(The search for `follow` reaches its candidate after 45 to 50 s of its 60 s budget; on a much
slower machine it may not, and the replay then reports a difference for step 39.)

### 13d. Ids from the size of the Map ([log](options-chain/40-place-overwrite.txt), [snapshot](options-chain/steps/40-place-overwrite/src/reducer.ts))

The first draft also dropped `nextId`: "the Map holds the orders by id, so the next id is one
more than the number of orders". Its `place`:

```ts
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  requires(validQty(qty));
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  // an accepted order is added exactly as the ticket says, under the next id ...
  ensures((r: ChainUi) => implies(accepts(u, qty, price), orderFor(r.orders.get(u.orders.size + 1), t, qty, price)));
  // ... and nothing else changes: one order more (none for a rejected one), the others kept
  ensures((r: ChainUi) => r.orders.size === (accepts(u, qty, price) ? u.orders.size + 1 : u.orders.size));
  ensures((r: ChainUi) => keepsOrders(u, r) && keepsAllHolds(u, r) && sameView(u, r));
  // the limit depends on the current state, so it is checked here, not at the dispatch site
  if (!accepts(u, qty, price)) return u;
  // ids are 1, 2, 3, …: the next one is one more than the number of orders
  const o: Order = { expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: new Map(u.orders).set(u.orders.size + 1, o) };
}
```

`orderFor(o, t, qty, price)` takes `Order | undefined` now, so the contract looks the new order
up with `get` instead of searching for it with `some` (Step 10's `r.orders.some((o) =>
orderFor(o, u.nextId, …))`).

```
$ vreact verify
…
Obligations by file
  ✓ src/model.ts                             22/22
  ✗ src/reducer.ts                           21/25
…
✗ src/reducer.ts:188:11  [postcondition] postcondition of place: implies(wellFormed(u), wellFormed(r))
    │ `grind` failed
…
    │ h₂₇ : …  (a long hypothesis, 3 lines: --full shows it)
    │ h : ((1 ≤ qty ∧ qty ≤ 500) ∧ 0 < price) ∧ model.openQty u.orders.values + qty ≤ 1000
    │ h_1 :
    │   -1 *
    │         model.openQty
    │           (u.orders.set (u.orders.size + 1)
    │               { expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.ask, qty := qty,
    │                 price := price }).values +
    │       1001 ≤
    │     0
    │ …
    │ ⊢ False
✗ src/reducer.ts:192:11  [postcondition] postcondition of place: r.orders.size === (accepts(u, qty, price) ? u.orders.size + 1 : u.orders.size)
    │ `grind` failed
…
    │ hcontract : u.orders.keys.Nodup
    │ h_1 : u.orders.size + 1 ∈ u.orders.keys
    │ w : model.Order
    │ h_3 : (u.orders.size + 1, w) ∈ u.orders.entries
…
✗ src/reducer.ts:193:11  [postcondition] postcondition of place: keepsOrders(u, r) && keepsAllHolds(u, r) && sameView(u, r)
…
✗ src/reducer.ts:206:11  [postcondition] postcondition of cancel: implies(wellFormed(u), wellFormed(r))
    │ `grind` failed
…
    │ h₃₀ :
    │   ((1 ≤ u.heat ∧ u.heat ≤ 5) ∧ ∀ (x : model.Order), x ∈ u.orders.values → (1 ≤ x.qty ∧ x.qty ≤ 500) ∧ 0 < x.price) ∧
    │     model.openQty u.orders.values ≤ 1000
    │ h : -1 * model.openQty (u.orders.delete id').values + 1001 ≤ 0
    │ ⊢ False

✗ NOT VERIFIED  146/150 obligations proved, 4 failed; components: 4/6 verified  (49.7s)
```

Four failures, of two kinds. Read the hypotheses first.

**A counterexample: the second failure.** `h_1` says that `u.orders.size + 1` is already a key,
and `h_3` names its order `w`. `hcontract` is a contract instance, as in Step 3: in vreact's
Lean library, a Map's `keys` has a contract of its own, that the keys are distinct. Nothing in
the invariant excludes `h_1`, and it is easy to reach: place two orders (ids 1 and 2), cancel
order 1. One order is left, under id 2, so `size + 1` is 2, and the next `place` *replaces*
order 2: `Map.set` on a present key overwrites its value, silently. The "one order more"
postcondition fails because the Map's size does not change, and the third failure
(`keepsOrders`) is the same counterexample: order 2 is no longer what it was. With an array,
`[...u.orders, o]` always grew; the same mistake would have produced a duplicate id, which the
old invariant's `distinct` ruled out.

**No counterexample: the first and the fourth.** The cap of Step 10 (the open quantity is at
most `MAX_OPEN` = 1000 lots) must survive `place` and `cancel`. In the first failure, `h` says
the old total plus the new quantity is at most 1000, and `h_1` says the total after `set` is
above 1000. Nothing relates the two totals: the
automation does not know what `set` does to a sum over the Map's values. In the fourth, `h₃₀`
says the old total is at most 1000, `h` says the total after `delete` is above 1000, and again
nothing relates them. Both claims are true (replacing an order of at least one lot by one of
`qty` lots cannot raise the total above the old total plus `qty`; deleting an order cannot
raise it at all), but they are facts about sums, which need induction. Step 10's lemmas in
`proofs/model.lean` (`openQty_append`, `openQty_filter_le`) are about lists: `place` appended
to a list, `cancel` filtered it. The Map needs its own.

### 13e. `nextId` back, and the cap lemmas for a Map ([log](options-chain/41-reducer-maps-verified.txt), [snapshot](options-chain/steps/41-reducer-maps-verified/src/reducer.ts), [proofs](options-chain/steps/41-reducer-maps-verified/proofs/model.lean))

The fix brings `nextId` back, and the invariant says again that every id in use is below it:

```ts
export function wellFormed(u: ChainUi): boolean {
  return (
    1 <= u.heat &&
    u.heat <= MAX_HEAT &&
    [...u.orders].every(([id, o]) => validOrder(o) && id < u.nextId) &&
    openQty([...u.orders.values()]) <= MAX_OPEN
  );
}
```

`place` sets the order under `u.nextId` and advances it. Its contract has to change in one
place, and that is a lesson of its own:

```ts
  ensures((r: ChainUi) => implies(accepts(u, qty, price), orderFor(r.orders.get(u.nextId), t, qty, price)));
  // ... and nothing else changes: one order more (none for a rejected one), the others kept.
  // Only where the next id is not in use, which the invariant says: Map.set would overwrite.
  ensures((r: ChainUi) =>
    implies(wellFormed(u), r.orders.size === (accepts(u, qty, price) ? u.orders.size + 1 : u.orders.size) && keepsOrders(u, r)),
  );
  …
  return { ...u, orders: new Map(u.orders).set(u.nextId, o), nextId: u.nextId + 1 };
```

Step 10's "one order more" held in every state: appending to an array always grows it. With a
Map it holds only where `nextId` is not a key yet, and that is what the invariant says. So the
claim is stated for well-formed states, `implies(wellFormed(u), …)`. This is the honest form of
the claim: in a state with an order under `nextId` (unreachable, but a value of the type), `place`
does overwrite it.

**The cap lemmas for a Map.** In Lean, `[...u.orders.values()]` is `u.orders.values`, the list
of the values of the Map's entries in insertion order, so `openQty` still sums a list. Two
lemmas say what `set` and `delete` do to that sum. They go into `proofs/model.lean`, next to
Step 10's list lemmas, which they use (`openQty_append`, `openQty_cons`, `openQty_nil`; the
list version of `openQty_filter_le` becomes a version over a Map's entries):

```lean
/-- `place` and the total: `set` on a key that is not in use appends the entry, so the total
grows by its quantity; on a key in use it replaces that entry's order in place. -/
theorem openQty_set (m : JSMap Int Order) (k : Int) (v : Order) :
    openQty (m.set k v).values
      = if k ∈ m.keys then openQty m.values - ((m.get k).getD v).qty + v.qty
        else openQty m.values + v.qty := by
  unfold JSMap.values
  rw [JSMap.entries_set]
  by_cases h : k ∈ m.keys
  · obtain ⟨o, ho⟩ := JSMap.entry_of_mem_keys h
    rw [JSMap.get_of_mem_entries ho]
    simp only [h, ite_true, Option.getD_some]
    exact openQty_map_update m.entries k v o m.nodup ho
  · simp only [h, ite_false, List.map_append, openQty_append, List.map_cons, List.map_nil, openQty_cons, openQty_nil]
    omega
…
/-- `cancel`: deleting an entry never raises the total, as long as no quantity is negative. -/
theorem openQty_delete_le (m : JSMap Int Order) (k : Int) (h : ∀ q ∈ m.entries, 0 ≤ q.2.qty) :
    openQty (m.delete k).values ≤ openQty m.values := by
  unfold JSMap.values
  rw [JSMap.entries_delete]
  exact openQty_filter_le _ _ h
…
grind_pattern OrdersMap.openQty_set => VTS.model.openQty (VReact.JS.JSMap.values (VReact.JS.JSMap.set m k v))
grind_pattern OrdersMap.openQty_delete_le => VTS.model.openQty (VReact.JS.JSMap.values (VReact.JS.JSMap.delete m k))
```

`openQty_map_update` (in the file, not shown) is the induction behind the "key in use" case:
replacing the one entry of a key changes the sum by the difference of the two quantities. The
`JSMap.…` lemmas (`entries_set`, `entries_delete`, `entry_of_mem_keys`, `get_of_mem_entries`)
come with vreact's Lean library (`VReact/JSMap.lean`), which models a JS Map as its list of
entries; `JSMap.set` is defined by the same two cases. The `grind_pattern`s (Step 10b)
make `grind` add a lemma whenever a goal mentions the total after a `set` or a `delete`. For
`place` it then splits on the `if`: the "key in use" branch contradicts the invariant (the key
is `u.nextId`, and every key in use is below it), the other branch is arithmetic.

`openQty_set` covers both cases on purpose. A first version
([probe](options-chain/probes/41-lemma-hypothesis/), not one of the steps) had only the second,
with the side condition `k ∉ m.keys` as a hypothesis. `grind` added it but did
not decide the membership, and `place`'s invariant obligation still failed. With the `if` in
the lemma's statement, `grind` splits on it. The "key in use" case is also what amending an
order needs (Step 16).

```
$ vreact verify
…
Obligations by file
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           25/25
…
✔ VERIFIED  150/150 obligations proved; components: 6/6 verified  (28.4s)
```

Same count as step 36, different contracts. What changed:

| step 36 (arrays) | step 41 (Maps and Sets) |
|---|---|
| `wellFormed`: `distinct(u.orders, (o) => o.id) && u.orders.every((o) => validOrder(o) && o.id < u.nextId)` | `[...u.orders].every(([id, o]) => validOrder(o) && id < u.nextId)`: keys are distinct by construction |
| `heldPrice(hs, id)` finds the first hold; `holdAt` puts the new hold first and filters out the old one | `u.held.get(id)`; `new Map(u.held).set(id, price)` |
| `keepsHolds`: every old hold of another expiry is still there (one direction, nested `some`) | `keepsHolds`: the other holds are unchanged, both directions, one `get` each |
| `place`: `r.orders.some((o) => orderFor(o, u.nextId, t, qty, price))` | `orderFor(r.orders.get(u.nextId), t, qty, price)`: a lookup |
| `keepsOrders`: nested `some` over seven fields | `[...u.orders].every(([id, o]) => sameOrder(o, r.orders.get(id)))` |
| `cancel`: `!r.orders.some((o) => o.id === id)`; the others kept "by id" | `!r.orders.has(id)`; the others unchanged, and no new ones (`keepsOrdersExcept`) |
| "one order more" holds in every state | holds where `nextId` is fresh: `implies(wellFormed(u), …)` |
| `<li key={o.id}>` needs `distinct` from the invariant | `<li key={id}>` from the Map's keys |

---

## Step 14: generic helpers

The frames of Step 13 compare Sets and Maps with the same few shapes: "the same members", "the
same members except `k`", "the same entries except at `k`". Each is a small function over
`ReadonlySet<int>` or `ReadonlyMap<int, int>`. Step 15 adds a second Set, of strikes, which
needs the same functions again, and other apps need them at other types. **Generic
functions** write them once ([snapshot](options-chain/steps/44-collections/src/collections.ts)):

```ts
export function sameMembers<K extends int | string>(a: ReadonlySet<K>, b: ReadonlySet<K>): boolean {
  return [...a].every((x) => b.has(x)) && [...b].every((x) => a.has(x));
}
```

A top-level function may have type parameters, each with at most one **constraint**:

* none: the values are opaque; they can be stored, passed and returned, but not compared;
* **equality**, `K extends int | string` (unions of `int`, `string`, `boolean`, string-literal
  enums): also `===` on `K`, `includes`, and `K` as a Map key or Set element;
* **fields**, `T extends { readonly id: int }`: also `x.id` on a `T`.

A generic function is **proved once for every type** its constraint allows, not once per call:
its body is checked with `K` abstract, so a contract that is true only at the app's own types is
not proved. Calls infer the type arguments from the VTS types of the arguments (where
TypeScript sees only `number`, VTS knows `int`). Callers of an `@opaque` generic function use
its contract at their own types.

The helpers go into a new module, `src/collections.ts`:

| helper | constraint | used for |
|---|---|---|
| `sameMembers(a, b)`, `sameMembersExcept(a, b, k)` | `K extends int \| string` | `collapsed` frames |
| `toggleIn(s, k)` (`@opaque`) | `K extends int \| string` | `toggle` |
| `sameEntries(a, b)`, `agreeExcept(a, b, k)` | `K extends int \| string`, `V`: see 14a | `held` frames |
| `sameList(a, b)` | `K extends int \| string` | the order of the working orders |
| `byId(xs, id)` (`@opaque`) | `T extends { readonly id: int }` | looking up an expiry (`labelOf`, the ticket's expiry) |

### 14a. One frame for every Map, and records ([log](options-chain/42-generic-records-rejected.txt), [snapshot](options-chain/steps/42-generic-records-rejected/src/))

The first draft of `collections.ts` leaves the value type unconstrained, so that the same frame
works for the holds (`ReadonlyMap<int, int>`) and for the orders (`ReadonlyMap<int, Order>`):

```ts
/** `a` and `b` have the same entries (in any order). */
export function sameEntries<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>): boolean {
  return [...a].every(([x, v]) => b.get(x) === v) && [...b].every(([x, v]) => a.get(x) === v);
}

/** `a` and `b` have the same entries, except perhaps at `k`: none dropped, none added, none changed. */
export function agreeExcept<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>, k: K): boolean { … }
```

and the reducer drops its own order frames (`sameOrder`, `keepsOrders`, `keepsOrdersExcept`)
for `sameEntries(u.orders, r.orders)` and `agreeExcept(u.orders, r.orders, id)`. TypeScript
accepts it. VTS does not:

```
$ vreact verify
✗ VTS src/collections.ts:29:35: === on values of the type parameter V is not supported: V has no equality constraint, and JS compares objects and arrays by identity (and numbers by IEEE rules); declare V extends int | string | boolean (or a string-literal enum type) to compare its values
```

The rejection is about the generic function itself, at the `===` in its body: it would be
checked once for every `V`, and for a record `V` the JS `===` means "the same object". For the
frames of this reducer that happens to hold (`new Map(u.orders)` copies the entries, and the
untouched values are the very same objects), but it is not what a frame means. An order
restored from a server or from `localStorage` (`JSON.parse`) is a new object with the same
fields, and `sameEntries` would call it changed; so would an update that rebuilds an order with
the same fields (`{ ...o }`). The Lean model has no object identity at all, so no translation
of this `===` would mean what it means in JS: VTS rejects it, as it rejects `===` on records
everywhere.

The fix follows the message. `V extends int | string | boolean` for the two value comparisons,
and the orders keep their field-by-field frames in `reducer.ts`. With the constraint,
TypeScript itself refuses `sameEntries(u.orders, r.orders)` ("Type 'Order' is not assignable to
type 'string | number | boolean'", [probe](options-chain/probes/42-constrained-records/)), so
the misuse cannot come back.

### 14b. The frames Part 1 could not afford, and a timeout ([log](options-chain/43-collections-timeout.txt), [snapshot](options-chain/steps/43-collections-timeout/src/))

With the helpers each missing frame is one line, so this step adds them all:

```ts
/** Frame condition: the same filter, focus and heat threshold, and the same expiries collapsed. */
export function sameView(u: ChainUi, r: ChainUi): boolean {
  return r.filter === u.filter && r.focus === u.focus && r.heat === u.heat && sameMembers(u.collapsed, r.collapsed);
}
…
/** Frame condition: the same working orders, listed in the same order, and the same next id. */
export function sameOrders(u: ChainUi, r: ChainUi): boolean {
  return r.nextId === u.nextId && sameList([...r.orders.keys()], [...u.orders.keys()]) && keepsOrders(u, r);
}

// toggle: only this expiry's collapse state changes
  ensures((r: ChainUi) => r.filter === u.filter && r.focus === u.focus && r.heat === u.heat);
  ensures((r: ChainUi) => sameMembersExcept(u.collapsed, r.collapsed, id) && sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, collapsed: toggleIn(u.collapsed, id) };
// holdAt, follow: only this expiry's hold changes
  ensures((r: ChainUi) => sameView(u, r) && agreeExcept(u.held, r.held, id) && sameOrders(u, r));
// jump: this expiry's collapse state and hold, and the focus
  ensures((r: ChainUi) => r.filter === u.filter && r.heat === u.heat);
  ensures((r: ChainUi) => sameMembersExcept(u.collapsed, r.collapsed, id) && agreeExcept(u.held, r.held, id) && sameOrders(u, r));
// setCollapsed, setFilter, setHeat: the same pattern; setHeat states its result exactly
  ensures((r: ChainUi) => r.heat === (1 <= t && t <= MAX_HEAT ? t : u.heat));
// cancel: the other orders keep their places in the list
  ensures((r: ChainUi) => sameList([...r.orders.keys()], [...u.orders.keys()].filter((k) => k !== id)));
// chainReducer: the next id only grows
  ensures((r: ChainUi) => r.nextId >= u.nextId);
```

`place` now promises where the new order appears: last in the list, with the others in their
places. `sameList` compares two lists element by element (`===` on arrays would compare
identity):

```ts
  ensures((r: ChainUi) =>
    implies(wellFormed(u) && accepts(u, qty, price), sameList([...r.orders.keys()], [...u.orders.keys(), u.nextId]) && keepsOrders(u, r)),
  );
  ensures((r: ChainUi) => r.nextId === (accepts(u, qty, price) ? u.nextId + 1 : u.nextId));
  // ... and nothing else changes; a rejected order changes nothing at all
  ensures((r: ChainUi) => implies(!accepts(u, qty, price), sameOrders(u, r)));
  ensures((r: ChainUi) => sameView(u, r) && sameEntries(u.held, r.held));
```

```
$ vreact verify
…
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           40/40
…
  ✗ src/OptionsChain.tsx                     36/37
…
✗ src/OptionsChain.tsx:151:11  [callback] OrderTicket.onSubmit handler (passed from OptionsChain) preserves the invariant of OptionsChain, assuming OrderTicket's callback contract
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
…
✗ NOT VERIFIED  170/171 obligations proved, 1 failed; components: 4/6 verified  (113.5s)
```

Every contract of the reducer is proved (40/40), including all the new frames. The failure is
in the chain, and it is a **timeout**: no counterexample, the automation ran out of its budget.
The handler of the ticket's Submit dispatches `place` and must keep the chain's invariant.
`chainReducer` is not `@opaque`, so the handler's goal contains `place(…)`, and every
postcondition of `place` is added to the goal. The handler needs only the first
(`wellFormed`), but the automation also processes the others, and `sameList` over
`[...u.orders.keys(), u.nextId]` is a statement about every index of a list built by appending:
in a goal that also holds the chain's whole render state, that is too much. This time the
report has no list of cases: the diagnosis of Step 12a lists cases only when the goal, once
prepared, splits into several, and the Submit handler has no branches, so its goal is one case.

The skill's usual advice, "make a large function `@opaque` with precise `ensures`", moves the
problem here: with `chainReducer` marked `@opaque`
([probe](options-chain/probes/43-opaque-reducer/), not one of the steps), the handler sees
only the reducer's two postconditions and is proved, but the reducer's own postcondition, which
uses every operation's contract in its nine cases, times out instead. Its diagnosis proves eight
of the nine cases; the one that does not finish is `h_8`, the `"place"` case. The fix is a lighter
statement. A position is cheap: the automation knows where `set` puts a key it appends
([snapshot](options-chain/steps/44-collections/src/reducer.ts)):

```ts
  ensures((r: ChainUi) =>
    implies(wellFormed(u) && accepts(u, qty, price), [...r.orders.keys()].indexOf(u.nextId) === u.orders.size && keepsOrders(u, r)),
  );
```

It says much less than the `sameList` version: the new order comes after as many orders as
there were before, and every old order is still there, unchanged. It no longer says that the
old orders keep their relative order, nor that no other order appears: Step 13e's "one order
more" went with the `sameList` claim. The first is listed under "Not proven here"; the second
comes back, in a cheaper form, in Step 18c. (For `cancel` the `sameList` version stays, and is
proved.)

### 14c. Proved once, used everywhere ([log](options-chain/44-collections.txt), [snapshot](options-chain/steps/44-collections/src/), [explain](options-chain/44-collections-explain.txt))

```
$ vreact verify
translated 8 module(s), 171 proof obligation(s) → .vreact/ ; checking with Lean…
…
Functions
  VERIFIED           sameMembers
  VERIFIED           sameMembersExcept
  VERIFIED           toggleIn
  VERIFIED           sameEntries
  VERIFIED           agreeExcept
  VERIFIED           sameList
  VERIFIED           byId
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           40/40
  ✓ src/StrikeRow.tsx                        22/22
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     37/37
  ✓ src/App.tsx                              20/20

✔ VERIFIED  171/171 obligations proved; components: 6/6 verified  (35.8s)
```

**What "proved once" looks like.** `vreact explain src/collections.ts` prints the Lean that
vreact generates for the module (saved as a [log](options-chain/44-collections-explain.txt), not
replayed). `toggleIn`, its contract and its proof are stated for every type `K`:

```ts
/**
 * Add `k` if it is missing, remove it if it is there.
 * @opaque
 */
export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) === !s.has(k));
  ensures((r: ReadonlySet<K>) => sameMembersExcept(s, r, k));
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}
```

```lean
def toggleIn {K : Type} [DecidableEq K] (s : (VReact.JS.JSSet K)) (k : K) : (VReact.JS.JSSet K) :=
  (let n : (VReact.JS.JSSet K) := s;
(if h₁ : (VReact.JS.JSSet.has n k) = true then (let n_1 : (VReact.JS.JSSet K) := (VReact.JS.JSSet.delete n k);
n_1) else (let n_1 : (VReact.JS.JSSet K) := (VReact.JS.JSSet.add n k);
n_1)))

theorem toggleIn.post {K : Type} [DecidableEq K] (s : (VReact.JS.JSSet K)) (k : K)  :
    ((VReact.JS.JSSet.has (VTS.collections.toggleIn (K := K) s k) k) = (!(VReact.JS.JSSet.has s k))) := by
  unfold toggleIn
  exact (/-⟦ob1⟧-/ by vreact_ob vreact_auto)
```

* `{K : Type}` is the type parameter: the theorem holds for every type `K` that meets the
  constraint below.
* `[DecidableEq K]` is the equality constraint: Lean may compare two `K`s, and nothing else is
  known about them. That is all the body may use, so the proof cannot depend on `K` being `Int`.
* The copy `new Set(s)` is just `s`: in the model a Set is a value, so copying is free, and each
  mutation of the fresh copy is a new binding (`n_1 := JSSet.delete n k`).

A field constraint becomes a parameter that reads the field:

```lean
def byId {T : Type} (T_id : T → Int) (xs : (List T)) (id' : Int) : (Option T) :=
  (xs.find? (fun (x : T) => (VReact.JS.eq (T_id x) id')))
```

`T_id` is "the `id` of a `T`". A caller passes the actual field, so `byId` cannot assume anything
else about `T`. At the call sites (from
[`vreact explain src/model.ts`](options-chain/44-collections-explain-model.txt) and
[`vreact explain src/reducer.ts`](options-chain/44-collections-explain-reducer.txt)) the type
arguments are filled in. In `model.ts`, `labelOf` now calls `byId(es, id)`:

```lean
  (let e : (Option VTS.model.Expiry) := (VTS.collections.byId (T := VTS.model.Expiry) (fun (x₃₅ : VTS.model.Expiry) => (x₃₅).id) es id');
```

and in `reducer.ts`, `toggle` and `holdAt`'s frame use `toggleIn` and `agreeExcept` at `Int`:

```lean
  ({ u with collapsed := (VTS.collections.toggleIn (K := Int) u.collapsed id') } : VTS.reducer.ChainUi)
  …
    ((((VTS.reducer.sameView u (VTS.reducer.holdAt u id' price)) = true) ∧ ((VTS.collections.agreeExcept (K := Int) (V := Int) u.held ((VTS.reducer.holdAt u id' price).held) id') = true)) ∧ ((VTS.reducer.sameOrders u (VTS.reducer.holdAt u id' price)) = true)) := by
```

**Obligations are counted once.** `collections.ts` has 6 obligations: the two postconditions of
`toggleIn`, the two of `byId`, and two index obligations inside `sameList` (`a[i]` and `b[i]` are
in range under `forall(0, a.length, …)`). They are proved once, in `collections.ts`, for every
type. The calls add none: `byId` is called in `model.ts` and in `OptionsChain.tsx`, `sameList`
in `sameOrders` (used by eight contracts of the reducer) and in `cancel`'s contract, and none of
these call sites has an obligation of its own, because the helpers have no `requires`. A caller
of the `@opaque` ones (`toggleIn`, `byId`) reasons with their `.post` theorems instantiated at
its own types.

**What the frames now say.** The reducer has 40 obligations, up from 25: the new ones are mostly
frames, plus `chainReducer`'s claim about `nextId`. Each operation now states what it does *and*
that it changes nothing else. Before and after:

| step 41 | step 44 |
|---|---|
| `toggle`, `setCollapsed`, `setFilter`, `jump`, `setHeat`: no frame (Part 1's list, Step 8) | each states what stays the same, field by field |
| `sameView`'s collapsed part: two `every … has` | `sameMembers(u.collapsed, r.collapsed)` |
| `keepsHolds(u, r, id)` | `agreeExcept(u.held, r.held, id)` |
| `keepsAllHolds(u, r)` (one direction) | `sameEntries(u.held, r.held)` (both directions) |
| `toggle`: a copy, `has`, `delete`/`add` | `toggleIn(u.collapsed, id)`, proved once |
| `cancel`: the other orders are kept | ... and keep their places in the list (`sameList`) |
| `place`: one order more, the others kept | the new order at position `u.orders.size` (`indexOf`), the others kept; no longer "one order more" |
| nothing about `nextId` across actions | `chainReducer`: `r.nextId >= u.nextId` (Part 1's list, Step 8) |
| `labelOf`: `es.find((x) => x.id === id)` | `byId(es, id)` |

The orders keep their own frames (`sameOrder`, `keepsOrders`, `keepsOrdersExcept`, `sameOrders`)
because `Order` is a record (14a).

The components changed only where they read the state; Steps 15 and 16 use the new structures
in the UI.

---

## Step 15: watched strikes

The quick filter shows a window of strikes around the ATM row. A trader often follows a few
strikes that are not near the money: a hedge, a strike with open orders. A **watched** strike
is shown in every expiry, whatever the filter. Each strike row gets a ☆ button in its strike
cell (★ when watched), and the toolbar lists the watched strikes, each a button that stops
watching it.

The state gets a Set of strike prices
([snapshot](options-chain/steps/46-watch/src/reducer.ts)):

```ts
export type ChainUi = {
  readonly collapsed: ReadonlySet<int>; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly watch: ReadonlySet<int>; // watched strikes: shown in every expiry, whatever the filter
  …
};
```

and an operation, written with the generic `toggleIn` of Step 14 (proved once, used here at
`K = int` without a new proof):

```ts
export function watchStrike(u: ChainUi, k: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.watch.has(k) === !u.watch.has(k));
  // ... and nothing else changes
  ensures((r: ChainUi) => r.filter === u.filter && r.focus === u.focus && r.heat === u.heat);
  ensures((r: ChainUi) => sameMembers(u.collapsed, r.collapsed) && sameMembersExcept(u.watch, r.watch, k));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, watch: toggleIn(u.watch, k) };
}
```

`sameView`, the frame of the operations that leave the view alone (`holdAt`, `follow`,
`place`, `cancel`), gets `sameMembers(u.watch, r.watch)`. `StrikeRow` gets two props,
`watched: boolean` and `onWatch: () => void`, and the button
([snapshot](options-chain/steps/46-watch/src/StrikeRow.tsx)):

```tsx
<td className="strike">
  <button
    className={props.watched ? "watch on" : "watch"}
    title={props.watched ? "Stop watching this strike" : "Watch this strike: show it in every expiry, whatever the filter"}
    onClick={() => props.onWatch()}
  >
    {props.watched ? "★" : "☆"}
  </button>
  {fmtPrice(s.strike)}
</td>
```

`onWatch` has no `callbackRequires`: it reports nothing, and the chain's handler for it
(`dispatch({ kind: "watch", strike: s.strike })`) is checked like every other handler, against
the chain's invariant. The toolbar renders the Set in ascending order, keyed by the strike
([snapshot](options-chain/steps/46-watch/src/OptionsChain.tsx)):

```tsx
{[...ui.watch].toSorted((a, b) => a - b).map((k) => (
  <button key={k} className="chip" title="Stop watching" onClick={() => dispatch({ kind: "watch", strike: k })}>
    ★ {fmtPrice(k)}
  </button>
))}
```

Its keys need no invariant: the members of a Set are distinct, and the automation knows that
`toSorted` keeps them distinct.

### 15a. Two lists joined ([log](options-chain/45-watch-dup-keys.txt), [full log](options-chain/45-watch-dup-keys-full.txt), [snapshot](options-chain/steps/45-watch-dup-keys/src/))

The first draft shows the filter's window, then the watched strikes:

```tsx
// the filter's window, and the watched strikes: they are shown whatever the filter
const rows = [...e.strikes.slice(span.lo, span.hi), ...e.strikes.filter((s) => ui.watch.has(s.strike))];
…
rows.map((s) => (
  <StrikeRow
    key={s.strike}
    …
```

```
$ vreact verify
…
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           45/45
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✗ src/OptionsChain.tsx                     41/42
  ✓ src/App.tsx                              20/20

Failed obligations
✗ src/OptionsChain.tsx:141:21  [unique-keys] keys s.strike are distinct across rows
    │ `grind` failed
…
✗ NOT VERIFIED  182/183 obligations proved, 1 failed; components: 4/6 verified  (75.3s)
```

A **unique-keys** obligation says that the keys of a rendered list are distinct (Part 1, Step
3). The short report keeps the hypotheses nearest the conclusion, and here those are about the
holds: the ones that matter are among the 29 it leaves out and the six it folds. The `--full`
log has them (excerpt, lines 289-295):

```
    │ right : Key.int w.strike = a
…
    │ left_1 : w_1 ∈ e.strikes
    │ left_2 : w_1.strike ∈ σ.ui.watch.elems
    │ right_2 : Key.int w_1.strike = b
    │ h_4 : a = b
```

Read as a counterexample: `w` is a row of the window (the hypothesis `left` above these lines
says `w ∈ JS.slice e.strikes …`), `w_1` is a strike of the ladder that is watched (`left_1`,
`left_2`), and their keys `a` and `b` are equal (`h_4`). That is a watched strike inside the
window: it is in both lists, so it is rendered twice, with the same key. With the filter at
"All" every watched strike is a duplicate. React warns about two children with the same key,
and calls what it then does on an update unsupported: it may show a row twice or drop one.
TypeScript has nothing to say about it.

The natural fix is one pass over the ladder, keeping a row when it is in the window or watched,
which also keeps the ladder's order. With the index of the row: `e.strikes.filter((s, i) =>
(span.lo <= i && i < span.hi) || ui.watch.has(s.strike))`. VTS rejects that
([probe](options-chain/probes/45-filter-index/), not one of the steps): "filter callbacks take
only the element in VTS (an index parameter is supported for map only, `xs.map((x, i) => …)`):
for a condition on positions write forall(0, xs.length, (i) => … xs[i] …)".

The window can be stated without positions: it is a set of strikes.

### 15b. The window as a Set ([log](options-chain/46-watch.txt), [snapshot](options-chain/steps/46-watch/src/OptionsChain.tsx))

```tsx
// the filter's window, and the watched strikes: they are shown whatever the filter. One
// pass over the ladder, in its order: a watched strike inside the window is one row.
const win = new Set(e.strikes.slice(span.lo, span.hi).map((s) => s.strike));
const rows = e.strikes.filter((s) => win.has(s.strike) || ui.watch.has(s.strike));
```

`rows` is now a filter of the ladder, and the chain's precondition says that the strikes of a
ladder are distinct (`validChain`, Part 1). A part of a list with distinct keys has distinct
keys: the automation knows that, so the obligation is proved.

```
$ vreact verify
…
  ✓ src/OptionsChain.tsx                     42/42
  ✓ src/App.tsx                              20/20

✔ VERIFIED  183/183 obligations proved; components: 6/6 verified  (37.7s)
```

Lesson: two lists joined are a list with duplicates as soon as they overlap. A `key` makes React
notice; the unique-keys obligation makes the verifier notice first.

---

## Step 16: amending an order

Each working order gets ▼ and ▲ buttons that move its price by one tick
([snapshot](options-chain/steps/49-amend/src/OptionsChain.tsx)):

```tsx
{[...ui.orders].map(([id, o]) => (
  <li key={id}>
    …
    {contractText(o.leg, o.strike)} @ {fmtPrice(o.price)}
    <span className="acts">
      <button title="Lower the price by one tick" disabled={o.price <= 1} onClick={() => dispatch({ kind: "amend", id: id, price: o.price - 1 })}>
        ▼
      </button>
      <button title="Raise the price by one tick" onClick={() => dispatch({ kind: "amend", id: id, price: o.price + 1 })}>
        ▲
      </button>
      <button onClick={() => dispatch({ kind: "cancel", id: id })}>Cancel</button>
    </span>
  </li>
))}
```

The reducer gets an action `{ kind: "amend"; id: int; price: int }` and an operation. Like
`place` (Step 10), `amend` checks its own rule: an unknown id or a price below one tick
changes nothing. The `disabled` on ▼ is for the user; the guard in the reducer is what keeps the
invariant (Part 1, Step 5b). Its contract says what changes and what stays the same, including
the order of the list:

```ts
/** `p` is the order `o` at the price `price`: the same contract, direction and quantity. */
export function repriced(o: Order | undefined, p: Order | undefined, price: int): boolean { … }

export function amend(u: ChainUi, id: int, price: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  // the order has the new price, and is otherwise the same order ...
  ensures((r: ChainUi) => implies(u.orders.has(id) && price > 0, repriced(u.orders.get(id), r.orders.get(id), price)));
  // ... the other orders are unchanged, and the list keeps its order
  ensures((r: ChainUi) => keepsOrdersExcept(u, r, id) && r.orders.has(id) === u.orders.has(id) && r.nextId === u.nextId);
  ensures((r: ChainUi) => sameList([...r.orders.keys()], [...u.orders.keys()]));
  ensures((r: ChainUi) => sameView(u, r) && sameEntries(u.held, r.held));
  const o = u.orders.get(id);
  if (o === undefined || price <= 0) return u;
  …
}
```

### 16a. A timeout ([log](options-chain/47-amend-timeout.txt), [full log](options-chain/47-amend-timeout-full.txt), [snapshot](options-chain/steps/47-amend-timeout/src/reducer.ts))

The first draft replaces the order: it takes the old one out and puts the amended one in.

```ts
  // replace the order: take the old one out, put the amended one in
  const orders = new Map(u.orders);
  orders.delete(id);
  orders.set(id, { ...o, price: price });
  return { ...u, orders: orders };
```

```
$ vreact verify
…
  ✗ src/reducer.ts                           48/50
…
✗ src/reducer.ts:256:11  [postcondition] postcondition of amend: implies(wellFormed(u), wellFormed(r))
    │ `grind` failed
    │ …
    │ h₄₃, h_1 : …  (2 long hypotheses, 13 lines: --full shows them)
    │ …
    │ h_4 : -1 * model.openQty u.orders.values + model.openQty (u.orders.delete id').values ≤ 0
    │ …
    │ ⊢ False
✗ src/reducer.ts:261:11  [postcondition] postcondition of amend: sameList([...r.orders.keys()], [...u.orders.keys()])
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
    │   … (the goal as stated: --full shows it)
    │ The goal splits into 3 cases. … Each case alone, smallest first, with up to 100000 heartbeats: 2 proved, 1 did not finish. The first that did not finish, case h_1.isFalse.isTrue:
    │ case h_1.isFalse.isTrue
    │   … (6 earlier hypotheses: u, id', price, hcontract✝⁴, p_1✝, heq✝: --full shows them)
    │ h✝² : ¬price ≤ 0
    │ …
    │ h✝ : ↑((List.filter (fun x => !JS.eq x id') u.orders.keys).length + 1) = ↑u.orders.keys.length
    │ …
    │ ⊢ ∀
    │     (x :
    │       { x //
    │   …

✗ NOT VERIFIED  190/192 obligations proved, 2 failed; components: 4/6 verified  (79.1s)
```

Two failures, neither with a counterexample. The short report folds or leaves out some of the
hypotheses that matter here; `vreact verify --full`
([full log](options-chain/47-amend-timeout-full.txt)) prints them:

```
$ vreact verify --full     # (excerpts, lines 107-114 and 911 of the log)
    │ h_1 :
    │   -1 *
    │         model.openQty
    │           ((u.orders.delete id').set id'
    │               { expiry := p_1.expiry, leg := p_1.leg, strike := p_1.strike, buy := p_1.buy, qty := p_1.qty,
    │                 price := price }).values +
    │       1001 ≤
    │     0
…
    │ heq✝ : u.orders.get id' = some p_1✝
```

The first is the cap. `h_1` says that the total after `delete` and then `set` is above
`MAX_OPEN`. The claim is true (the order comes back with the same quantity), but Step 13e's
lemma about `delete` is an inequality: the total does not grow (`h_4` is that lemma, for this
Map). Adding the order back adds its quantity, so all the automation can conclude is "at most
the old total plus this quantity", which may be above `MAX_OPEN`. Nothing in
`proofs/model.lean` says that deleting an order lowers the total by exactly its quantity.

The second is a **timeout**, like Step 14b's. There, the claim was true and only too heavy for
the goal it appeared in. The diagnosis of Step 12a narrows it down: two of the three cases are
proved, and the third, `h_1.isFalse.isTrue`, does not finish within its share either. In that
case the order is found (`heq✝`, in the full log) and the price is positive (`h✝²`), so the
code replaces the order, and the two lists have the same length (`h✝`, the first test of
`sameList`). (A `✝` marks a name that the proof cannot refer to.) What is left, the goal cut off
here and printed whole in the full log, is the second test of `sameList`: the same key at every
position. A timeout says nothing either way: the automation stopped before it found a proof or
a counterexample. One way to find out is to ask a narrower question, a consequence of the claim
that is cheaper to check.

### 16b. A narrower claim ([log](options-chain/48-amend-moves.txt), [full log](options-chain/48-amend-moves-full.txt), [snapshot](options-chain/steps/48-amend-moves/src/reducer.ts))

The list keeps its order, so in particular the amended order keeps its place:

```ts
  ensures((r: ChainUi) => sameList([...r.orders.keys()], [...u.orders.keys()]));
  // (a narrower claim, implied by the one above: the amended order keeps its place)
  ensures((r: ChainUi) => [...r.orders.keys()].indexOf(id) === [...u.orders.keys()].indexOf(id));
```

```
$ vreact verify
…
✗ src/reducer.ts:263:11  [postcondition] postcondition of amend: [...r.orders.keys()].indexOf(id) === [...u.orders.keys()].indexOf(id)
    │ `grind` failed
…
✗ NOT VERIFIED  190/193 obligations proved, 3 failed; components: 4/6 verified  (82.4s)
```

This one fails with hypotheses. Two of them, from the `--full` log (excerpt):

```
    │ h_1 :
    │   ¬JS.indexOf
    │         ((u.orders.delete id').set id'
    │             { expiry := p_1.expiry, leg := p_1.leg, strike := p_1.strike, buy := p_1.buy, qty := p_1.qty,
    │               price := price }).keys
    │         id' =
    │       JS.indexOf u.orders.keys id'
…
    │ h_10 :
    │   List.Pairwise (fun x1 x2 => ¬x1 = x2) ((u.orders.delete id').keys ++ [id']) =
```

`h_1` is the negated claim: the amended order is at another position. `h_10` shows where:
the keys of the result are those of `u.orders.delete id'`, followed by `id'`. The amended order
is now **last**. This is JS's insertion order (Step 13): `delete` forgets the key, its
position with it, and `set` of a key that is not in the Map appends it. In the app: amend the
first of three working orders, and it jumps to the bottom of the list. In plain JavaScript:

```js
const m = new Map([[1, "a"], [2, "b"], [3, "c"]]);
const n = new Map(m); n.delete(1); n.set(1, "A");
[...n.keys()];                       // [2, 3, 1]: key 1 moved to the end
[...new Map(m).set(1, "A").keys()];  // [1, 2, 3]: set alone keeps its place
```

So the `sameList` claim was false as well, and its timeout hid a real bug. The narrower claim
found it.

### 16c. `set` alone ([log](options-chain/49-amend.txt), [snapshot](options-chain/steps/49-amend/src/reducer.ts))

`set` on a key that is in use replaces the value where it is. The fix drops the `delete`, and
the narrower claim with it (`sameList` says more):

```ts
  // set on a key in use replaces the value where it is: the order keeps its place in the list
  return { ...u, orders: new Map(u.orders).set(id, { ...o, price: price }) };
```

```
$ vreact verify
…
  ✓ src/reducer.ts                           50/50
…
  ✓ src/OptionsChain.tsx                     46/46
…
✔ VERIFIED  192/192 obligations proved; components: 6/6 verified  (42.6s)
```

Both failures are gone. The cap is proved by Step 13e's `openQty_set`, whose "key in use" case
covers this: the order's quantity is taken out and the same quantity put back. The
order of the list is proved because the automation knows that `set` on a key in use leaves the
keys as they are. The chain's handlers of ▼ and ▲ keep its invariant through `chainReducer`,
as every other dispatch does.

Lesson: a timeout is not a verdict. When a claim times out, check a narrower consequence of it;
when that one fails, the counterexample usually explains the whole claim.

---

## Step 17: a second mutation audit

Part 1, Step 7 broke the code on purpose and kept the spec: a change that still verifies (a
**surviving mutant**) shows something the spec does not say. One of Part 1's gaps (Step 8)
was frames: `toggle`, `jump` and three other operations did not say what they
leave alone. Step 14 added those frames with the generic helpers. This audit checks that they
now catch what they should, and looks for what still gets through. Each mutant below is a small
change to step 49 (snapshot `49-amend`).

### 17a. Three mutants caught ([log](options-chain/50-mutants-caught.txt), [full log](options-chain/50-mutants-caught-full.txt), [snapshot](options-chain/steps/50-mutants-caught/src/reducer.ts))

```ts
// toggle: collapsing an expiry also clears the focus
return { ...u, collapsed: toggleIn(u.collapsed, id), focus: null };
// holdAt: holding an expiry also holds the focused expiry at the same price
const held = new Map(u.held);
held.set(id, price);
if (u.focus !== null) held.set(u.focus, price);
return { ...u, held: held };
// cancel: the remaining orders are listed by expiry
return { ...u, orders: new Map([...u.orders].filter(([k]) => k !== id).toSorted(([, a], [, b]) => a.expiry - b.expiry)) };
```

```
$ vreact verify
…
Failed obligations
✗ src/reducer.ts:113:11  [postcondition] postcondition of toggle: r.filter === u.filter && r.focus === u.focus && r.heat === u.heat
    │ `grind` failed
…
    │ h : ¬none = u.focus
…
✗ src/reducer.ts:160:11  [postcondition] postcondition of holdAt: sameView(u, r) && agreeExcept(u.held, r.held, id) && sameOrders(u, r)
    │ `grind` failed
…
    │ h_1 : (fst, snd) ∈ u.held.entries
    │ left : ¬fst = id'
    │ right : ¬(if fst = focus then some price else if fst = id' then some price else u.held.get fst) = some snd
    │ h_3 : fst = focus
…
✗ src/reducer.ts:277:11  [postcondition] postcondition of cancel: implies(wellFormed(u), wellFormed(r))
…
✗ src/reducer.ts:281:11  [postcondition] postcondition of cancel: sameList([...r.orders.keys()], [...u.orders.keys()].filter((k) => k !== id))
    │ `grind` failed
…
✗ NOT VERIFIED  188/192 obligations proved, 4 failed; components: 4/6 verified  (54.1s)
```

All three are caught, by the frames of Step 14:

* `toggle`: `h` says that the focus was not `null` before; after the toggle it is. Part 1's
  `toggle` had no frame, and this mutant would have survived there.
* `holdAt`: `h_1` is a hold of another expiry (`left`: `fst` is not `id'`), and `h_3` says it
  is the focused expiry. `right` says that its hold after the operation is not what it was: it
  moved to `price`. That is the case where the focused expiry was already held, at another
  price. Where it was not held, the mutant adds a hold, and only the second direction of
  `agreeExcept` ("no hold added") catches that; Part 1's one-way `keepsHolds` ("every other hold
  is still there") did not say it.
* `cancel`: the order of the list. In the full log, `h_3` says that the two key lists differ at
  a position `val`, and `h_4 : val ≤ 0` with `left : -1 * val ≤ 0` make it position 0: after the
  sort, the first order is no longer the first of the old list. The cap obligation of this
  `cancel` fails too, without a counterexample: the total of a re-sorted Map is the same, but no
  lemma says so (the claim is true, and moot).

One more thing in this log: the chain, the App and the certificate are `INCOMPLETE`, with
`sorryAx` among the certificate's axioms. In Part 1, Step 7, a failed `place` postcondition did
not reach the certificate. The difference is in the toggle mutant. A failed obligation is
admitted as a whole (its proof is `sorry`), and toggle's failed postcondition is a conjunction
that also says `r.heat === u.heat`. The automation used that part to prove that the chain's
invariant (the heat threshold is 1–5) still holds after a toggle. Two probes (not steps)
confirm it: with the toggle mutant alone the certificate is `INCOMPLETE`
([probe](options-chain/probes/50-toggle-alone/)); with the heat equality in an `ensures` of its
own, the same mutant fails only `toggle`'s focus claim, and the chain and the certificate are
`VERIFIED` ([probe](options-chain/probes/50-toggle-split/)). The holdAt mutant alone makes only
`holdAt` and `chainReducer` `INCOMPLETE` (the reducer's "the next id only grows" uses holdAt's
`sameOrders`; [probe](options-chain/probes/50-holdat-alone/)). Tip: when a failure
reaches further than expected, look for a conjunction in the failed `ensures`; split into
separate `ensures`, the report shows which part the other proofs use.

### 17b. Four mutants survive ([log](options-chain/51-mutants-survive.txt), [snapshot](options-chain/steps/51-mutants-survive/src/))

Four more, again on step 49:

```ts
// reducer.ts, setFilter: a new filter clears the watched strikes
return { ...u, filter: f, watch: new Set() };
```

```tsx
// OptionsChain.tsx, the rows: only watched strikes inside the window
const rows = e.strikes.filter((s) => win.has(s.strike) && ui.watch.has(s.strike));
// OptionsChain.tsx, the ▲ button: it lowers the price
<button title="Raise the price by one tick" onClick={() => dispatch({ kind: "amend", id: id, price: o.price - 1 })}>
// StrikeRow.tsx, the star: ☆ for a watched strike, ★ for the others
{props.watched ? "☆" : "★"}
```

```
$ vreact verify
…
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             22/22
  ✓ src/reducer.ts                           50/50
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✓ src/App.tsx                              20/20

✔ VERIFIED  192/192 obligations proved; components: 6/6 verified  (44.2s)
```

All four survive. They are of three kinds.

**A frame that lists fields.** `setFilter`'s frame says
`r.focus === u.focus && r.heat === u.heat && sameMembers(u.collapsed, r.collapsed)`, plus the
holds and the orders. It was written in Step 14, before `watch` existed. Step 15 added `watch`
to `sameView`, but five operations (`toggle`, `setCollapsed`, `setFilter`, `jump`, `setHeat`)
change a view field, so they do not use `sameView`: they list the fields they keep, one by
one, and `watch` is not on any of these lists. A frame that lists fields says nothing about a
field added later.

**What is rendered.** The rows mutant shows no strike outside the window, and only the watched
ones inside it. Nothing states which rows are shown: the chain's obligations are about keys,
indices and preconditions, all of which still hold. The same goes for the star (Part 1's list,
Step 8: that the content on screen matches the data).

**Wiring.** ▲ lowers the price. The reducer does exactly what it is asked (`amend` to
`o.price - 1`); which button asks for what is the chain's wiring, like the cells of Part 1,
Step 7.

### 17c. A stronger spec ([log](options-chain/52-mutants-spec.txt), [snapshot](options-chain/steps/52-mutants-spec/src/))

Two changes, with the four mutants still in the code.

**Frames by exception.** `sameView` stays the one list of the view's fields. An operation that
changes some of them says "the same view, except these":

```ts
/**
 * Frame condition: the same filter, focus and heat threshold, the same expiries collapsed and
 * the same strikes watched. The one list of the view's fields: an operation that changes some of
 * them states its frame as `sameView(u, { ...r, field: u.field })`, "the same view, except
 * this field", so a field added here is in every frame.
 */
…
// toggle
  ensures((r: ChainUi) => sameView(u, { ...r, collapsed: u.collapsed }) && sameMembersExcept(u.collapsed, r.collapsed, id));
// setFilter
  ensures((r: ChainUi) => sameView(u, { ...r, filter: u.filter }));
// jump
  ensures((r: ChainUi) => sameView(u, { ...r, collapsed: u.collapsed, focus: u.focus }) && sameMembersExcept(u.collapsed, r.collapsed, id));
```

`{ ...r, filter: u.filter }` is `r` with `u`'s filter put back: if that is the same view as `u`,
then `r` differs from `u` at most in the filter. (In Lean it is `{ r with filter := u.filter }`.)
`setCollapsed`, `watchStrike` and `setHeat` get the same form.

**Which rows to show, as a function with a contract.** JSX has no contract of its own, so the
choice of rows moves into the model, where a function can say what it returns:

```ts
/**
 * The strike rows an expiry shows: the rows of the filter's window, and every watched strike,
 * whatever the filter. One pass over the ladder, in its order, so a watched strike inside the
 * window is one row.
 */
export function shownRows(ks: readonly Strike[], span: Span, watch: ReadonlySet<int>): readonly Strike[] {
  // every row of the window is shown, and every watched strike ...
  ensures((r: readonly Strike[]) => ks.slice(span.lo, span.hi).every((s) => r.some((x) => x.strike === s.strike)));
  ensures((r: readonly Strike[]) => ks.every((s) => !watch.has(s.strike) || r.some((x) => x.strike === s.strike)));
  // ... and nothing else, each strike once
  ensures((r: readonly Strike[]) => r.every((x) => watch.has(x.strike) || ks.slice(span.lo, span.hi).some((s) => s.strike === x.strike)));
  ensures((r: readonly Strike[]) => implies(distinct(ks, (s) => s.strike), distinct(r, (s) => s.strike)));
  const win = new Set(ks.slice(span.lo, span.hi).map((s) => s.strike));
  return ks.filter((s) => win.has(s.strike) && watch.has(s.strike));
}
```

(The mutant's `&&` moved along with the code.) The chain calls
`const rows = shownRows(e.strikes, span, ui.watch);`. The contract is about what `shownRows`
returns. That the chain then renders exactly `rows`, for the right window and only for an open
expiry, is still plain JSX that no contract describes.

```
$ vreact verify
…
Obligations by file
  ✓ src/collections.ts                       6/6
  ✗ src/model.ts                             24/26
  ✗ src/reducer.ts                           48/49
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✓ src/App.tsx                              20/20

Failed obligations
✗ src/model.ts:154:11  [postcondition] postcondition of shownRows: ks.slice(span.lo, span.hi).every((s) => r.some((x) => x.strike === s.strike))
    │ `grind` failed
…
    │ h : s ∈ JS.slice ks span.lo (some span.hi)
…
✗ src/model.ts:155:11  [postcondition] postcondition of shownRows: ks.every((s) => !watch.has(s.strike) || r.some((x) => x.strike === s.strike))
    │ `grind` failed
…
    │ left : s.strike ∈ watch.elems
…
✗ src/reducer.ts:136:11  [postcondition] postcondition of setFilter: sameView(u, { ...r, filter: u.filter })
    │ `grind` failed
…
    │ h : x ∈ u.watch.elems
    │ ⊢ False

✗ NOT VERIFIED  192/195 obligations proved, 3 failed; components: 6/6 verified  (44.9s)
```

Two of the four are caught now. (The reducer has one obligation fewer than in step 51:
`watchStrike`'s two frame `ensures` became one.) `setFilter`: `h` says that some strike `x` was
watched before, and the frame says it must still be. `shownRows`: `h` is a row of the window,
and `left` a watched strike, that the result leaves out. The ▲ mutant and the star survive, as
expected: they are wiring and display, which no contract here describes. This time the chain,
the App and the certificate stay `VERIFIED`: no proof of an invariant used the failed claims.

### 17d. The app after the audit ([log](options-chain/53-audited.txt), [snapshot](options-chain/steps/53-audited/src/))

Snapshot 53 removes the mutants and keeps the stronger spec of 17c.

```
$ vreact verify
translated 8 module(s), 195 proof obligation(s) → .vreact/ ; checking with Lean…
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             26/26
  ✓ src/reducer.ts                           49/49
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✓ src/App.tsx                              20/20

✔ VERIFIED  195/195 obligations proved; components: 6/6 verified  (43.0s)
```

195 obligations, 65 functions, 6 components and 8 verified files, plus the proof file with 8
lemmas (`proofs/model.lean` is unchanged since Step 13e: amending needed no new lemma). This was
the final app until someone who had not written its specification read it.

---

## Step 18: an outside review

Both audits so far (Steps 7 and 17) were done by the author of the spec, who knew what each
contract was meant to say. For snapshot 53, a reviewer who had not written it read the spec
next to the code and did the same thing as those audits: make small changes to the code, run
them against the unchanged spec, and keep the ones that still verify. They were saved as probes
on snapshot 53, two of them with several changes in one probe. The report listed those
changes, a partial fix for one of them, and code comments that claim more than the contracts
prove.

A report like this is answered finding by finding. Each finding is one of three kinds:

1. **A gap a contract can close.** Write the contract, and check that it catches the
   reviewer's change.
2. **A gap a contract can only narrow.** The contract makes a function exact, but something
   outside it is still trusted: plain code around the function can still pass it the wrong
   value, or a function that the new contract is written with can still be wrong.
3. **A gap out of reach.** VTS contracts do not describe what a component renders or which value
   a handler passes on, and a function that the spec itself is written with can only be trusted
   as written. Such a finding goes into "Not proven here", stated as precisely as possible.

The answer takes four snapshots: the reviewer's changes together (18a); a stronger spec, with
the changes still in the code, to see which it catches (18b); the same spec without them
(18c); and the fixes of what 18c reports, which are the final app of Step 19. Section 18d
lists what remains out of reach, and where each change ends up.

### 18a. Fourteen changes that verify ([log](options-chain/54-review-mutants.txt), [snapshot](options-chain/steps/54-review-mutants/src/))

The reviewer's changes to snapshot 53, each verified in the probe named on its row (195/195
every time; changes 2 and 3 share one probe, and changes 9 to 12 another):

| # | change | where | probe |
|---|---|---|---|
| 1 | `place` also files the new order under the id below it, when that id is free (a cancelled order's id) | `place` | [53-place-extra-order](options-chain/probes/53-place-extra-order/) |
| 2 | the cap refuses an order that brings the total to exactly 1000: `+ qty < MAX_OPEN` | `accepts` | [53-rules-changed](options-chain/probes/53-rules-changed/) |
| 3 | the "3" filter shows four rows on each side: `levelsOf` returns 4 for it | `levelsOf` | [53-rules-changed](options-chain/probes/53-rules-changed/) |
| 4 | Pause and Rally do nothing: both toggles `return s` | `simReducer` | [53-pause-rally-noop](options-chain/probes/53-pause-rally-noop/) |
| 5 | a rally tick pauses the feed while the rally is off | `simReducer` | [53-rally-tick-pauses](options-chain/probes/53-rally-tick-pauses/) |
| 6 | the futures move ten times the offset: `shiftQuote(e.future, d * 10)` | `moveFutures` | [53-futures-times-ten](options-chain/probes/53-futures-times-ten/) |
| 7 | the random walk never moves: `f.offset` in both branches | `stepFeed` | [53-walk-frozen](options-chain/probes/53-walk-frozen/) |
| 8 | Submit sends 1 lot (`props.onSubmit(1, price)`) of the opposite side, whatever the ticket shows | `OrderTicket`, the chain's `onSubmit` | [53-submit-sells](options-chain/probes/53-submit-sells/) |
| 9 | "Collapse all" and "Expand all" swapped | the chain | [53-chain-wiring](options-chain/probes/53-chain-wiring/) |
| 10 | the strike window ignores a held price (`center` is always the live price) | the chain | [53-chain-wiring](options-chain/probes/53-chain-wiring/) |
| 11 | strike rows rendered only for collapsed expiries (`!open &&`) | the chain | [53-chain-wiring](options-chain/probes/53-chain-wiring/) |
| 12 | ☆ watches the next strike up (`s.strike + 20`) | the chain | [53-chain-wiring](options-chain/probes/53-chain-wiring/) |
| 13 | every expiry renders its whole ladder (`e.strikes.map`) | the chain | [53-rows-whole-ladder](options-chain/probes/53-rows-whole-ladder/) |
| 14 | the working orders listed newest first (`.toReversed()`) | the chain | [53-orders-reversed](options-chain/probes/53-orders-reversed/) |

The partial fix was for change 1: `r.orders.size === u.orders.size + 1` for an accepted order
from a well-formed state, which verifies, 196/196
([probe](options-chain/probes/53-place-one-more/)). The comments: `chainReducer`'s `ids are
never reused` (change 1 files an order under an old id), `simReducer`'s `so "never move" is not
a fix` (change 7 is a walk that never moves), and the first line of `reducer.ts`, which still
calls the reducer total, though Step 9 gave it a precondition.

Snapshot 54 has all fourteen changes at once; they touch different lines. It still verifies:

```
$ vreact verify
…
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             26/26
  ✓ src/reducer.ts                           49/49
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✓ src/App.tsx                              20/20

✔ VERIFIED  195/195 obligations proved; components: 6/6 verified  (43.7s)
```

Changes 1–7 are in functions that have contracts (`place`, `levelsOf`, `simReducer`,
`moveFutures` and `stepFeed`) or that a contract calls (`accepts`, which has none of its own:
`place`'s contract names it). Those contracts say less than the code does, and 18b tries to
close each of these gaps. Changes 8–14 are in the components: which value a handler passes on,
and which list a JSX expression renders. Those are the third kind; 18d comes back to them.

### 18b. A stronger spec, with the changes still in ([log](options-chain/55-review-spec.txt), [full log](options-chain/55-review-spec-full.txt), [snapshot](options-chain/steps/55-review-spec/src/))

Snapshot 55 is snapshot 54 with a stronger spec: the fourteen changes are still in the code.
The new contracts, function by function:

```ts
// reducer.ts
/**
 * The state with the ticket's order added under the next id, without the check: the state that
 * `place` builds when it accepts, written out again for `place`'s contract.
 */
export function withOrder(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  const o: Order = { expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: new Map(u.orders).set(u.nextId, o), nextId: u.nextId + 1 };
}
…
  // ... no other order is added or changed ...
  ensures((r: ChainUi) => implies(accepts(u, qty, price), keepsOrdersExcept(u, r, u.nextId)));
…
  // the rule is the invariant's: from a well-formed state, an order is refused only when the
  // state with it would not be well-formed
  ensures((r: ChainUi) => implies(wellFormed(u) && !accepts(u, qty, price), !wellFormed(withOrder(u, t, qty, price))));
…
// chainReducer
  // the next id only grows ...
  ensures((r: ChainUi) => r.nextId >= u.nextId);
  // ... and every new order gets an id at or above the old next id and below the new one. With
  // the line above, by induction over the actions: no id is ever given to two orders.
  ensures((r: ChainUi) => [...r.orders].every(([k]) => u.orders.has(k) || (u.nextId <= k && k < r.nextId)));
```

* **`place`: no other order.** `keepsOrdersExcept` is the frame that `amend` and `cancel`
  already use: every order other than the one at the given id is unchanged, none dropped and
  none added. With the next id as that id, an accepted order is the only change to the orders.
  This rules out change 1. The reviewer's partial fix would rule it out too, but only for an
  accepted order from a well-formed state, and only by counting: with `place`'s other
  postconditions, one order more means exactly the one under the next id. The comment that
  change 1 contradicts, "ids are never reused", is about the reducer and a whole run of
  actions, so the spec states which orders may change (this frame) and, in the reducer, where a
  new order's id comes from (the next point).
* **`chainReducer`: no id given twice.** The old comment said "ids are never reused", but the
  contract below it only said that the next id never goes down. The new claim says where a new
  order's id comes from: if an order is in the result `r` and was not in `u`, its id is at least
  `u.nextId` and below `r.nextId`. That is a fact about one action. Over a run of actions it
  means that no id is given out twice: if an id `k` is given out by one action, then `k` is
  below the next id after it; a later action starts from a next id that is at least as large
  (the next id never goes down), so it can only give out ids above `k`. Lean checks the fact
  about one action; this two-line induction over the run is not checked by Lean.
* **`place`: the cap is the invariant's.** `accepts` is a function the spec calls, so it is
  part of the specification (Step 10). A stricter rule changes the guard and the contract
  together, and change 2 verifies. The new claim ties `accepts` to something written
  separately, the invariant: an order is refused only when the state with it added would not be
  well-formed. `place`'s first postcondition already says the other half: an accepted order
  keeps the state well-formed. Together, `accepts` is exactly as strict as `wellFormed`. A rule
  added to `accepts` alone now fails this claim; it must also go into `wellFormed`, where it
  holds for every state. `withOrder` builds "the state with the order added": it is `place`'s
  own construction, written out again, because the contract needs that state also when `place`
  refuses the order and returns `u`. Nothing ties the two copies together, so `withOrder` is
  one more function that the spec trusts as written (18d comes back to this).

```ts
// model.ts
export function levelsOf(f: StrikeFilter): int | null {
  ensures((r: int | null) => r === null || r >= 1);
  // the filter does what its button says: the label is the number of rows on each side
  ensures((r: int | null) => filterLabel(f) === (r === null ? "All" : `${r}`));
…
// App.tsx
/** `r` is the market `q` moved by d ticks: a missing side stays missing, the quantities stay. */
export function shifted(q: Quote, r: Quote, d: int): boolean {
  return r.bid === (q.bid === null ? null : q.bid + d) && r.ask === (q.ask === null ? null : q.ask + d) && r.bidQty === q.bidQty && r.askQty === q.askQty;
}
…
  // every expiry, in its place, with its futures market moved by exactly d ticks
  ensures((r: readonly Expiry[]) => r.length === es.length && forall(0, es.length, (i) => r[i].id === es[i].id && shifted(es[i].future, r[i].future, d)));
…
export function stepFeed(f: Feed): Feed {
  ensures((r: Feed) => implies(validFeed(f), validFeed(r)));
  // one draw of the generator, and a move of exactly as many ticks as it drew (0, 1 or 2)
  ensures((r: Feed) => r.seed === nextSeed(f.seed));
  ensures((r: Feed) => Math.abs(r.offset - f.offset) === Math.abs((nextSeed(f.seed) % 5) - 2));
```

* **`levelsOf`: what the button says.** The filter buttons show `filterLabel(f)`. The claim
  ties the two tables together: the label of a filter is its number of rows on each side. This
  is aimed at change 3; 18c shows what became of it.
* **`moveFutures`: exact about the futures.** As many expiries as it is given, with the same ids
  in the same places, each with its futures market moved by exactly `d` ticks. `shifted` states
  that for one market, independently of `shiftQuote`, which computes it. This rules out change
  6. It says nothing about the rest of an expiry (its label, symbol and strikes) beyond
  `validChain`, which is all the chain needs from them; "Not proven here" lists this gap.
* **`stepFeed`: one draw, and a move of its size.** Each step draws one number from the
  generator, and moves the offset by exactly as many ticks as the draw says (`seed % 5 - 2` is
  −2 to +2), up or down. A walk that never moves breaks the second claim whenever the draw is
  not zero: change 7. What the claims leave open is the direction (inside the band, either one
  would satisfy them) and the generator itself, `nextSeed`.

```ts
// App.tsx, simReducer
  // ... and while running, a tick is exactly one step of the random walk
…
  // a rally tick never draws from the generator, and at the top of the band it changes nothing
  ensures((r: Sim) => implies(a.kind === "rallyTick", r.feed.seed === s.feed.seed && (s.feed.offset < MAX_MOVE || r.feed.offset === s.feed.offset)));
  // each button flips its own flag and leaves the feed alone; nothing else changes a flag
  ensures((r: Sim) => r.paused === (a.kind === "togglePause" ? !s.paused : s.paused));
  ensures((r: Sim) => r.rally === (a.kind === "toggleRally" ? !s.rally : s.rally));
  ensures((r: Sim) => implies(a.kind === "togglePause" || a.kind === "toggleRally", sameFeed(r.feed, s.feed)));
```

**`simReducer`: every field, for every action.** The result of `simReducer` has four fields:
the feed's `offset` and `seed`, and the flags `paused` and `rally`. A reducer's contract is
complete when, for every action and every state, some postcondition fixes each field of the
result. A table of actions by fields shows where snapshot 53 left gaps:

| action | `offset`, `seed` | `paused`, `rally` |
|---|---|---|
| `tick` | fixed: unchanged while paused, otherwise one step of `stepFeed` | not mentioned |
| `rallyTick` | unchanged while paused or with the rally off; while climbing, `offset` + 1, but `seed` not mentioned; at the top of the band, not mentioned | not mentioned |
| `togglePause`, `toggleRally` | fixed while paused (unchanged); while running, not mentioned | not mentioned |

Changes 4 and 5 live in the last column. The four new postconditions fill every gap: a rally
tick never touches the seed and changes nothing at the top of the band; each button flips its
own flag and nothing else does; the two buttons leave the feed alone. With them, the contract
of `simReducer` describes its result completely. The comment that said "so 'never move' is not
a fix" now says only what that postcondition says: a tick, while running, is exactly one step of
`stepFeed`. Snapshot 55 also rewords the first line of `reducer.ts`: the reducer is "total in
the state, with a precondition on the action only".

```
$ vreact verify
…
  ✗ src/model.ts                             26/27
  ✗ src/reducer.ts                           49/52
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✗ src/App.tsx                              28/32

Failed obligations
✗ src/App.tsx:97:11  [postcondition] postcondition of moveFutures: r.length === es.length && forall(0, es.length, (i) => r[i].id === es[i].id && shifted(es[i].future, r[i].future, d))
    │ `grind` failed
    │ …
    │ w : Int
    │ h_8 : ¬(fun h₁ => some (10 * d + w)) = fun h₃ => some (d + w)
    │ …
    │ h_15 : ¬d + bid_1 = 10 * d + bid_1
    │ ⊢ False
✗ src/App.tsx:118:11  [postcondition] postcondition of stepFeed: Math.abs(r.offset - f.offset) === Math.abs((nextSeed(f.seed) % 5) - 2)
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
…
✗ src/App.tsx:155:11  [postcondition] postcondition of simReducer: r.paused === (a.kind === "togglePause" ? !s.paused : s.paused)
    │ `grind` failed
…
    │ left : s.paused = true
    │ right : (!s.paused) = false
    │ ⊢ False
✗ src/App.tsx:156:11  [postcondition] postcondition of simReducer: r.rally === (a.kind === "toggleRally" ? !s.rally : s.rally)
…
✗ src/model.ts:184:11  [postcondition] postcondition of levelsOf: filterLabel(f) === (r === null ? "All" : `${r}`)
    │ `grind` failed
    │ case grind
    │ r : Int
    │ hcontract : 4 ≥ 1
    │ heq : some 4 = some r
    │ h : ¬{ units := [51] } = JS.str r
    │ ⊢ False
✗ src/reducer.ts:239:11  [postcondition] postcondition of place: implies(accepts(u, qty, price), keepsOrdersExcept(u, r, u.nextId))
    │ `grind` failed
…
    │ h_1 : 1 < u.nextId
    │ h_2 : ¬u.nextId - 1 ∈ u.orders.keys
    │ h_3 : model.openQty u.orders.values + qty + qty ≤ 1000
…
    │ heq : u.orders.get (u.nextId - 1) = none
    │ ⊢ False
✗ src/reducer.ts:245:11  [postcondition] postcondition of place: implies(wellFormed(u) && !accepts(u, qty, price), !wellFormed(withOrder(u, t, qty, price)))
    │ `grind` failed
…
✗ src/reducer.ts:333:11  [postcondition] postcondition of chainReducer: [...r.orders].every(([k]) => u.orders.has(k) || (u.nextId <= k && k < r.nextId))
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
…
✗ NOT VERIFIED  203/211 obligations proved, 8 failed; components: 6/6 verified  (143.3s)
```

There are 16 new obligations (211 instead of 195), and 8 of them fail. The 16 are one new
postcondition in `model.ts`, three in `reducer.ts`, and twelve obligations in `App.tsx`: its
seven new postconditions, four index obligations for the `r[i]` and `es[i]` that
`moveFutures`'s `forall` reads, and one for the `% 5` in `stepFeed`'s contract (a divisor must
not be zero). Six failures catch the reviewer's changes.

**`place`, no other order** (line 239). `h_1` to `h_3` are the conditions of the change's
branch: the next id is above 1, the id below it is not in use, and there is room for the order
twice. `heq` says that id has no order before; after the change it has one. Change 1.

**`place`, the cap** (line 245). The short report folds the two hypotheses that make the
counterexample, `h₃₇` and `right_8`, into one line; the full log has them:

```
$ vreact verify --full     # (excerpt, lines 2720-2749 of the log)
✗ src/reducer.ts:245:11  [postcondition] postcondition of place: implies(wellFormed(u) && !accepts(u, qty, price), !wellFormed(withOrder(u, t, qty, price)))
…
    │ h₃₇ :
    │   (((1 ≤ u.heat ∧ u.heat ≤ 5) ∧
    │         ∀ (x : Int × model.Order),
    │           x ∈ u.orders.entries → ((1 ≤ x.snd.qty ∧ x.snd.qty ≤ 500) ∧ 0 < x.snd.price) ∧ x.fst < u.nextId) ∧
    │       model.openQty u.orders.values ≤ 1000) ∧
    │     ¬(((1 ≤ qty ∧ qty ≤ 500) ∧ 0 < price) ∧ model.openQty u.orders.values + qty < 1000)
…
    │ left_2 : -1 * qty + 1 ≤ 0
    │ left_3 : qty + -500 ≤ 0
    │ left_4 : -1 * price + 1 ≤ 0
…
    │ right_8 :
    │   model.openQty
    │         (u.orders.set u.nextId
    │             { expiry := t.expiry, leg := t.leg, strike := t.strike, buy := JS.eq t.side model.Side.ask, qty := qty,
    │               price := price }).values +
    │       -1000 ≤
    │     0
```

`h₃₇` is a well-formed state and an order that the changed rule refuses. `left_2` to `left_4`
say that the quantity and the price are valid, and `right_8` that the total with the order
added is at most 1000. Since the rule refused it, the total is not below 1000: it is exactly
1000. The changed rule refuses that order, though the state with it is well-formed. Change 2.

**`moveFutures`** (line 97). `h_8` says that a futures bid `w` becomes `10 * d + w` where the
claim wants `d + w`. The last lines make the same comparison for a bid named `bid_1`, and `h_15`,
the two results differ, holds for every `d` but 0: any move is a counterexample. Change 6.

**`stepFeed`** (line 118): a timeout. The claim is false for the frozen walk of change 7, which
moves 0 ticks where the draw says 1 or 2. But the automation runs out of budget in the
arithmetic of `%` before it finds a counterexample, as with the random walk of Step 12a; the
diagnosis tries both cases of the goal and finishes neither. Change 7 is caught, as a timeout
rather than with a counterexample.

**`simReducer`, the flags** (lines 155 and 156). The goal names no action, and there is no `a`
among its hypotheses: the automation has already split the reducer's `switch` into one goal per
action, and the report does not say which goal this is (`grind.1` is again `grind`'s own name).
The claim tells. `left` is a paused state (`right` says the same in another form: `!s.paused`
is false). From a paused state, no action of the changed reducer unpauses the feed, and the
claim expects the flag to stay as it is for every action but `togglePause`, for which it
expects `!s.paused`. So this is the `togglePause` goal: the changed reducer returns the state
as it is, still paused. Change 4, and the same for `rally`. Change 5 breaks the first of the two
as well, in a running state, but the report shows one counterexample per obligation. Change 5 alone, on the final app, fails it
([probe](options-chain/probes/57-rally-tick-pauses/)).

Two failures are not catches. In `levelsOf` (line 184), `heq` says `r` is 4, and `h` that the
text `{ units := [51] }` differs from `JS.str r`, the text of `r`. A JS string is a list of
UTF-16 code units, and 51 is the code of the character `3`. So the label is "3" and the levels
are 4, which looks like change 3. But without the change, in 18c, the claim fails the same way.
`chainReducer`'s new claim (line 333) is a timeout, and 18c has it too.

Changes 8 to 14, in the components, all still verify (`OrderTicket.tsx` 12/12,
`OptionsChain.tsx` 46/46): no contract here was meant to catch them. The certificate stays
`VERIFIED`: App's invariant uses only `simReducer`'s first postcondition.

### 18c. Two claims not proved ([log](options-chain/56-review-unproved.txt), [full log](options-chain/56-review-unproved-full.txt), [snapshot](options-chain/steps/56-review-unproved/src/))

Snapshot 56 is snapshot 55 without the reviewer's changes:

```
$ vreact verify
…
  ✓ src/collections.ts                       6/6
  ✗ src/model.ts                             26/27
  ✗ src/reducer.ts                           51/52
…
  ✓ src/App.tsx                              32/32

Failed obligations
✗ src/model.ts:184:11  [postcondition] postcondition of levelsOf: filterLabel(f) === (r === null ? "All" : `${r}`)
    │ `grind` failed
    │ case grind
    │ r : Int
    │ hcontract : 3 ≥ 1
    │ heq : some 3 = some r
    │ h : ¬{ units := [51] } = JS.str r
    │ ⊢ False
✗ src/reducer.ts:330:11  [postcondition] postcondition of chainReducer: [...r.orders].every(([k]) => u.orders.has(k) || (u.nextId <= k && k < r.nextId))
    │ (deterministic) timeout: the automation did not finish within this obligation's budget of 1000000 heartbeats (set "heartbeats" in vreact.json to change it)
…
    │ The goal splits into 11 cases. … Each case alone, smallest first, with up to 100000 heartbeats: 10 proved, 1 did not finish. The first that did not finish, case h_9:
    │ case h_9
    │   … (10 earlier hypotheses: u, tup✝, hcontract✝¹¹, hcontract✝¹⁰, ticket✝, qty✝, price✝, h_pre✝¹, …: --full shows them)
    │ hcontract✝⁸ : (List.map Prod.fst (place u ticket✝ qty✝ price✝ ⋯).orders.entries).Nodup
    │ hcontract✝⁷, hcontract✝⁶, hcontract✝⁵, hcontract✝⁴, hcontract✝³, hcontract✝², hcontract✝¹, hcontract✝ : …  (8 contract instances, 130 lines: --full shows them)
…
    │ ⊢ tup✝.fst ∈ u.orders.keys ∨ u.nextId ≤ tup✝.fst ∧ tup✝.fst < (place u ticket✝ qty✝ price✝ ⋯).nextId

✗ NOT VERIFIED  209/211 obligations proved, 2 failed; components: 6/6 verified  (112.5s)

$ vreact verify --full     # one of the 10 earlier hypotheses (excerpt, line 129 of the log)
    │ a✝ : tup✝ ∈ (place u ticket✝ qty✝ price✝ ⋯).orders.entries
```

App.tsx's new claims are all proved, and so are `place`'s. Two claims are not, and both are
true.

**The decimal text of a number.** Now `heq` says `r` is 3, and `h` that the text "3" differs from
the text of `r`. That is false, so the claim holds: the counterexample is not one. Lean defines
the text of a number with its `toString`, and the automation does not evaluate it, so it cannot
see that the text of 3 is "3". Four one-line lemmas, one per number, would fill the gap. It is
simpler to make the claim unnecessary: compute the label from the levels, so that, with this
code, the two cannot disagree ([snapshot](options-chain/steps/57-final-2/src/)):

```ts
/** A filter button's label: the number of rows it shows on each side, so the two cannot disagree. */
export function filterLabel(f: StrikeFilter): string {
  const n = levelsOf(f);
  return n === null ? "All" : `${n}`;
}
…
            <button key={f} className={ui.filter === f ? "on" : ""} onClick={() => dispatch({ kind: "filter", filter: f })}>
```

The buttons' keys change from the label to the filter itself (`key={f}`, a value of the enum
`StrikeFilter`): with computed labels, the proof that the keys are distinct would again need the
text of the numbers. The labels on screen are the same as before. What this gives up is the
claim aimed at change 3, which would have caught it once proved; it never was (18b). Change 3
itself now changes the label too: a `levelsOf` that returns 4 for the first filter puts "4" on
its button, and that verifies ([probe](options-chain/probes/57-levels-changed/)). The label
follows the number only because `filterLabel`'s code computes it, though, and no contract
checks that code: put snapshot 53's table of labels back into `filterLabel`, add change 3, and
the "3" button shows four rows, and that verifies too
([probe](options-chain/probes/57-label-3-shows-4/)). Whether the filters should be 3, 7, 11 and
99 is a product decision, and only a contract that repeats the numbers could check it.

**A fact several steps away.** The diagnosis of the timeout proves 10 of the reducer's 11 cases.
The one it does not finish is `h_9`, the `"place"` case: the goal asks whether an order `tup✝`
of `place`'s result (`a✝`, which the short report leaves out and the
[full log](options-chain/56-review-unproved-full.txt) shows) has an id of `u` or a fresh one.
The facts it has are `place`'s postconditions, eight of them in this case, 130 lines in the full
log. Its two frames hold under opposite conditions: `keepsOrdersExcept` when `accepts` holds,
`sameOrders` when it does not. So the automation must split on `accepts`, and for an accepted
order go from `keepsOrdersExcept` ("every order other than the new one is the same order as
before, field by field") to "the id is a key of `u`", several steps. Why this case does not
finish while the other ten are proved was not isolated: those cases have frames too, eight of
them the same `sameOrders` that a refused order gets, but there the frame holds without a
condition, among fewer postconditions. Step 14b had the opposite problem: there a postcondition the caller did
not need slowed the caller down. Here the caller needs a fact that the callee's contract
implies only in several steps. The fix states
that fact itself in `place`'s contract, in the words the reducer uses
([snapshot](options-chain/steps/57-final-2/src/reducer.ts)):

```ts
/**
 * Every order of `r` that `u` does not have got an id from `u.nextId` up to, not including,
 * `r.nextId`: an id that `u`'s next id had not handed out yet, and that `r`'s next id has passed.
 */
export function freshIds(u: ChainUi, r: ChainUi): boolean {
  return [...r.orders].every(([k]) => u.orders.has(k) || (u.nextId <= k && k < r.nextId));
}
…
  // ... no other order appears (the only new id can be the old next id) ...
  ensures((r: ChainUi) => freshIds(u, r));
…
  // ... and every new order gets an id at or above the old next id and below the new one. With
  // the line above, by induction over the actions: no id is ever given to two orders.
  ensures((r: ChainUi) => freshIds(u, r));
```

The first `freshIds` is `place`'s, the second the reducer's. For `place`, which raises the next
id by at most one, it says that the only order that can be new is under the old next id. That
rules out change 1 as well, so `place` no longer needs `keepsOrdersExcept`
([probe](options-chain/probes/57-place-extra-order/): change 1 on the final app fails only
`freshIds`). In the reducer's `"place"` case the fact is now one step from the goal.

### 18d. What no contract here closes

Changes 8 to 14 verify on the final app as they did on snapshot 53. They are of the third
kind: the chain's wiring and rendering. One of them deserves a closer look, because it is the
one that matters most to a user of the widget.

**Submit (change 8).** The ticket keeps the quantity and the price in its own state, and passes
them to `onSubmit`. A callback contract is written before the component's hooks, so it can
mention the props and the callback's arguments, but never the component's state: a
`callbackRequires(props.onSubmit, (qty, price) => …)` cannot compare `qty` with the quantity
the ticket shows. The chain then builds the `place` action from its own `ticket` and the two
arguments, and the only check on a dispatched action is the reducer's precondition, which may
mention only the action (Step 9, for a good reason: the state it meets is not known at the
dispatch). So no contract can compare the action with what the ticket shows. Moving the ticket's quantity and
price into the reducer's state would not close the gap either: the action would then carry no
data, but the ticket would show those values through its props, and what a component renders is
not specified. On the final app, change 8 verifies
([probe](options-chain/probes/57-submit-sells/)).

**The rows and the orders (changes 11, 13, 14).** Step 17c already moved the choice of rows
into `shownRows`, with a contract. Change 13 simply does not call it, and change 11 renders
its rows under the wrong condition. A list function with a contract about its order would not
help with change 14 either: `[...ui.orders]` is already exactly the Map's key order, and the
change reverses the list in the JSX, where it could reverse a function's result just as well.
All three verify on the final app ([probe](options-chain/probes/57-rows-whole-ladder/),
[probe](options-chain/probes/57-orders-reversed/),
[probe](options-chain/probes/57-chain-wiring/), which also has changes 9, 10 and 12).

**What only narrowed** (the second kind). `moveFutures` is now exact about the futures, but App
calls `moveFutures(EXPIRIES, offset)` in its render, in plain code: `offset * 10` there verifies
([probe](options-chain/probes/57-futures-call-site/)). `stepFeed` now draws once and moves by
the size of the draw, but the generator is still trusted as written: a `nextSeed` that returns
its argument unchanged draws the same number forever, so every step moves the futures one tick
down, until they bounce back and forth at the bottom of the band; that verifies, 209/209 (the
`%` in `nextSeed` and its obligation are gone) ([probe](options-chain/probes/57-seed-stuck/)).
And `accepts` is now tied to `wellFormed`, which leaves the invariant itself as the statement
of the rule: the cap of 1000 lots is right if `wellFormed` says the right thing, and if
`withOrder` builds the state that `place` builds. Nothing checks the second: a `withOrder` that
files the order with one lot more than it has lets the stricter cap of change 2 verify again
([probe](options-chain/probes/57-withorder-one-more/)).

**The fourteen changes, at the end.** Each change of 18a, with its kind and what the final app
does with it (each caught change alone on the final app is a probe in "Try it yourself"):

| change | kind | on the final app |
|---|---|---|
| 1: `place` files another order | 1 | caught by `place`'s `freshIds` (18c) |
| 2: a stricter cap | 2 | caught by the claim that ties `accepts` to `wellFormed`; `wellFormed` and `withOrder` are trusted as written |
| 3: the "3" filter shows four rows | 3 | verifies, with "4" on the button; the claim aimed at it is gone (18c), and the label follows the number only through `filterLabel`'s code |
| 4 and 5: Pause, Rally and the rally tick | 1 | caught: `simReducer`'s contract fixes every field of its result |
| 6: the futures moved ten times the offset | 2 | caught in `moveFutures`; its call in App is plain code |
| 7: a walk that never moves | 2 | caught, as a timeout (18b); the generator `nextSeed` is trusted as written |
| 8 to 14: the components | 3 | still verify (the probes above) |

---

## Step 19: the final app

### 19a. Verified ([log](options-chain/57-final-2.txt), [snapshot](options-chain/steps/57-final-2/src/))

The final app is snapshot 57: the spec of 18b with the two fixes of 18c, and none of the
reviewer's changes. `examples/options-chain` is this snapshot.

```
$ vreact verify
translated 8 module(s), 210 proof obligation(s) → .vreact/ ; checking with Lean…

Components
  VERIFIED           PriceCell              src/StrikeRow.tsx:12
  VERIFIED           StrikeRow              src/StrikeRow.tsx:41
  VERIFIED           TermRow                src/TermRow.tsx:19
  VERIFIED           OrderTicket            src/OrderTicket.tsx:19
  VERIFIED           OptionsChain           src/OptionsChain.tsx:34
  VERIFIED           App                    src/App.tsx:172
Functions
…
  VERIFIED           freshIds
…
  VERIFIED           withOrder
  VERIFIED           place
…
  VERIFIED           shifted
  VERIFIED           moveFutures
…
App certificates (VReact.run_allInv instantiated)
  VERIFIED           VTS.App.App.certificate  axioms: propext, Classical.choice, Quot.sound
Obligations by file
  ✓ src/collections.ts                       6/6
  ✓ src/model.ts                             26/26
  ✓ src/reducer.ts                           52/52
  ✓ src/StrikeRow.tsx                        24/24
  ✓ src/TermRow.tsx                          12/12
  ✓ src/OrderTicket.tsx                      12/12
  ✓ src/OptionsChain.tsx                     46/46
  ✓ src/App.tsx                              32/32

✔ VERIFIED  210/210 obligations proved; components: 6/6 verified  (69.9s)
```

210 obligations, 68 functions, 6 components and 8 verified files, plus one proof file with 8
lemmas. Since step 53: 15 more obligations (3 in `reducer.ts`, the 12 of 18b in `App.tsx`;
`model.ts` has the same 26, since the label claim went away) and three more functions (`freshIds`,
`withOrder`, `shifted`). `proofs/model.lean` is unchanged since Step 13e: the new contracts
needed no new lemma.

### 19b. Final checks

* **Verification.** `✔ VERIFIED 210/210` ([log](options-chain/57-final-2.txt), above). The
  certificate's axioms are exactly `propext, Classical.choice, Quot.sound`: the lemmas of the
  proof file are proved, not assumed. No `@trusted`, no `assume`, no `sorry` and no `hole`
  anywhere. `vreact synth src/model.ts` and `vreact synth src/reducer.ts` both report
  `no hole<T>() in …` ([probe](options-chain/probes/57-no-holes/)).
* **TypeScript.** `npx tsc --noEmit -p .` is clean in a project with the app's npm
  dependencies installed (`npm ci` from its `package-lock.json`).
* **Build** (by hand; no log is saved). `npx vite build`: 39 modules, `index.html` 0.41 kB, CSS
  4.03 kB, JS 167.27 kB (53.16 kB gzipped).
* **The contracts at run time** ([probe](options-chain/probes/57-runtime-contracts/): the
  script, its command and its outputs). `vreact/spec` records the `ensures` of a function when
  its test mode is on (synth uses that, Part 1, Step 1b). The script runs 300 random sessions
  of 60 actions from `INITIAL_UI`, then 20,000 random states (also unreachable ones: negative
  quantities, ids at or above `nextId`) with a random action each, every action both through
  `chainReducer` and by calling its operation directly; then `shownRows` on 20,000 random
  windows and watch lists, and `toggleIn` on Sets of strings; then the feed of `App.tsx`: 300
  random runs of 60 actions through `simReducer` from App's initial state, and 20,000 random
  (also invalid) feeds, each through `simReducer` with a random action and through `stepFeed`,
  and `moveFutures` on random offsets. All with real JS Maps and Sets. It evaluates each
  function's own postconditions on its result: 775,792 checks, no failure. It also checks that
  the working orders always stay in id order (placement order) in the sessions, and that
  `shownRows` keeps the ladder's order. An earlier version of the script computed its random
  numbers in floating point and lost their low bits, so that, for example, every random order
  was a sell; the script now uses a 32-bit generator, and its runs on earlier snapshots were
  made again with it. On the snapshots of Steps 16 and 17 it reports the step-47 draft of 16a
  and the mutants of 17a and 17c, and nothing for those of 17b, as the verifier does. On step 55
  it reports changes 1 and 4 to 7 of the review through the new postconditions of `place`,
  `chainReducer`, `simReducer`, `moveFutures` and `stepFeed`. It does not report change 2: random
  states almost never make the total exactly 1000, where the changed rule differs. The proof
  does not depend on luck.
* **In a browser** (by hand; no log is saved). This session was run on snapshot 53. The final
  app behaves the same: its code changes since then are postconditions, whose lambdas run only
  in test mode; three functions that only contracts call (`freshIds`, `withOrder`, `shifted`);
  the filter labels, which are now computed and read the same; and the filter buttons' keys,
  now the filters themselves (Step 18c). On the built app
  (`vite preview`), with the feed paused: the filter set to "All", ☆ on 96.00 and on 108.00
  (these two clicks from a script in the page, the others with the mouse), the filter set to
  "3". Every expiry then showed 96.00, its seven window rows and 108.00, in ladder order; the
  toolbar showed "Watching ★ 96.00 ★ 108.00". ☆ on 103.00, inside the window, made it ★ and left
  it one row. Two orders placed from the ladder, then ▲ on the first: its price went from 2.25
  to 2.30 and it stayed first. The console showed no errors.

---

## What exactly is proven

`App.certificate` is a Lean theorem: in every run of the application, meaning any sequence of
clicks and other user events, effect runs and timer firings in vreact's model of React 18, every
mounted component instance satisfies its invariant. Lean's kernel checked it, and it depends on
no assumption beyond Lean's standard axioms. In terms of this app, together with the 210
obligations of its components and functions, all proved, the final app guarantees the
following. *(Part 2)* marks what is new since step 26, and *(Step 18)* what the answer to the
outside review added.

**State that can never go wrong**

* The UI state is always well-formed: the heat threshold is 1–5 ticks. Every working order has
  a quantity of 1–500 lots and a positive price. Every order id in use is below `nextId`; the
  ids are the keys of a Map, so they are distinct by construction. The working orders together
  hold at most `MAX_OPEN` = 1000 lots *(Part 2, Steps 10 and 13e)*.
* An open ticket always has a positive price. The order ticket's own quantity and price are
  always valid.
* The simulated feed's offset stays within ±40 ticks, whatever the interleaving of timer
  ticks, re-renders and clicks. `moveFutures` moves each futures market by exactly the offset
  it is given *(Step 18)*; that App gives it the feed's offset is plain code (see "Not proven
  here").
* Each of these survives any new props the parent passes, including expiries disappearing.

**Rendering never fails** (in any reachable state, for any valid data):

* every array index is in bounds (e.g. the ATM row, at both edges of the ladder);
* every called function's precondition holds (`strikeWindow`'s ATM row, `heatOf`'s threshold);
* every division is by a non-zero number (price and volatility formatting);
* every list's keys are distinct (expiry ids; the strike rows, also with the watched strikes
  added to the window; the working orders, keyed by the Map's keys; the watched-strike chips;
  the filter and lot buttons);
* every child's precondition holds (`StrikeRow` gets a valid threshold, `OrderTicket` a
  positive price, the chain valid data).

**What the callbacks report, and what is dispatched**

* A price cell's button reports exactly the price the cell is given to show, its `price` prop
  (`PriceCell`). That the text it shows is that price is rendering, which is not specified.
* Every report from `StrikeRow` is consistent: the price is the current quote of the leg (call
  or put) and the side (bid or ask) that it names. The same holds for `TermRow` and the futures
  market. This rules out forwarding a cell's price under the wrong side or leg, the bug of
  snapshot 18 (Step 5a). It does *not* tie a report to the cell that was clicked: snapshot 24
  (Step 7a) has a call-bid cell that reports the put's ask, and it verifies. The chain then
  builds the ticket from the report and the row's strike; that step is plain code, and no
  contract says more about the ticket than that its price is positive.
* `OrderTicket` submits only valid orders.
* Every action the chain dispatches satisfies the reducer's precondition: an order is for 1–500
  lots. This is proved at each of the 14 `dispatch(…)` calls in `OptionsChain.tsx`, from the
  values the handler sees, so it holds for whatever state React applies the action to
  *(Part 2, Step 9)*.
* Every callback a parent hands to a child keeps the parent's invariant.

**What each operation of the reducer does when it is called** (the `ensures` in `reducer.ts`,
each proved for all inputs). Which operation the reducer's `switch` calls for an action is plain
code: see "Not proven here".

* `place` adds an order exactly when `accepts` holds: a valid quantity, a positive price, and a
  total that stays within `MAX_OPEN` (Step 10). From a well-formed state, `accepts` refuses an
  order only when the state with it added would not be well-formed *(Step 18)*: with "an
  accepted order keeps the state well-formed", it is exactly as strict as the invariant. (The
  state with it added is the one `withOrder` builds, a second copy of `place`'s construction
  that the spec trusts as written.) The order under the old `nextId` is then exactly the one
  that the `Ticket` passed to `place` describes (its expiry, contract and strike, buy for an ask
  and sell for a bid), with the quantity and the price passed along, and `nextId` goes up by
  one. (That the chain passes the
  ticket, quantity and price that the order ticket shows is plain code: see "Not proven
  here".) No other order appears: the only id that can be new is the old `nextId` *(Step 18)*.
  From a well-formed state, the new order's id comes at position `u.orders.size` of the Map's
  key order (after as many orders as there were before, so last), and every working order is
  still there, unchanged. A rejected order changes neither the orders nor `nextId`. `place`
  never changes the view (filter, focus, heat threshold, collapsed expiries, watched strikes) or
  the holds.
* `amend` with a known id and a positive price gives that order the new price, with the same
  contract, direction and quantity, at the same place in the Map's key order *(Part 2, Step
  16)*. For any id and price, the other orders are unchanged, no order is added or removed, the
  keys keep their order, and `nextId`, the view and the holds stay the same.
* `cancel` removes the order. The others are unchanged and keep their order in the Map *(Part
  2)*, no order is added, and `nextId`, the view and the holds stay the same.
* `holdAt` and `follow` set or clear one expiry's hold. The other expiries' holds are unchanged:
  none dropped, and *(Part 2)* none added or moved. The view, the orders and `nextId` stay the
  same.
* `toggle`, `setCollapsed`, `setFilter`, `watchStrike`, `jump` and `setHeat` each state what
  they change (one expiry's collapse state; exactly the given expiries collapsed; the filter;
  one strike's watch state; the expiry expanded, unlocked and focused; the threshold, if it is
  in range) and that nothing else changes *(Part 2, Steps 14b and 17c: in Part 1 these
  operations, except `watchStrike`, which did not exist yet, had no frame conditions)*. Their
  frames name the view's fields in one place, `sameView`, so a field added to the view later
  is in every frame.
* `chainReducer` keeps the invariant for every valid action and never lowers `nextId` *(Part
  2)*, and every order it adds gets an id at or above the old `nextId` and below the new one
  *(Step 18)*. Together these mean that no id is handed out twice in a run of actions: the id
  of a cancelled order never goes to a new one. Lean proves the two facts about one action; the
  step from them to a whole run is a two-line induction (Step 18b), which Lean does not check.
  (These facts are about handing out ids. That an id keeps the same order is up to the frames
  of the operations, and has two gaps: `amend` with a price below one tick, and the reducer's
  `switch`; see "Not proven here".)

**The generic helpers** (`collections.ts`, Part 2): `toggleIn` flips the membership of one key
and keeps every other member; `byId` returns a value with the id, or `undefined` only when no
element has it. (Its body can only return an element of `xs`, since it has no way to build a
`T`, but the contract does not say so, and callers of the `@opaque` `byId` see only the
contract.) Each is proved once, for every type its constraint allows, and used at `int`
(and at `Expiry`) without a new proof.

**Functional properties of the model** (the `ensures`, each proved for all inputs):

* `atmIndex`: in range. When it reports a row, that strike is a nearest strike to the price (no
  strike is strictly nearer), whatever the order of the ladder. It reports a row whenever a
  nearest strike exists.
* `strikeWindow`: in range, contains the ATM row, and contains *exactly* the rows within
  `levels` rows of it.
* `shownRows` *(Part 2, Step 17c)*: for every row of the filter's window and every watched
  strike of the ladder, the result has a row with that strike; every row of the result has a
  strike that is in the window or watched; and no strike appears twice when the ladder's
  strikes are distinct. Rows are compared only by their strike (see "Not proven here").
* `heatOf`: the colour is exactly the documented one for every edge, threshold and missing
  quote.
* `midPrice`: the mid rounded down when two-sided, otherwise the side present, otherwise null.
  When the market is two-sided and not crossed (bid ≤ ask), the result lies within the spread.
* `levelsOf`: at least one row on each side, or all rows. (The filter buttons' labels are
  computed from it in plain code since Step 18; see "Not proven here".)
* `stepFeed` *(Step 18)*: it preserves validity, draws exactly one number from the generator
  (`nextSeed`), and moves the offset by exactly as many ticks as the draw says (0, 1 or 2), up
  or down.
* `moveFutures` *(Step 18)*: it preserves validity, and returns as many expiries as it is
  given, with the same ids in the same order, each with its futures market moved by exactly the
  given number of ticks (a missing side stays missing, the quantities stay). It says nothing
  else about an expiry: its label, symbol and strikes are only kept valid (see "Not proven
  here").

**The rules of the simulated feed** (`simReducer` in `App.tsx`, Part 2, Step 12, completed in
Step 18): the feed stays valid; while paused, no action changes the feed; while running, a tick
is exactly one step of the random walk (`stepFeed`); a rally tick leaves the feed unchanged
while the rally is off, adds exactly one tick to the offset while the rally is on, the feed
runs and the offset is below the top of the band, changes nothing at the top of the band, and
never touches the generator's seed; Pause and Rally each flip their own flag and leave the feed
alone, and no other action changes a flag *(Step 18)*. Together these fix every field of the
result for every action and every state: the postconditions describe `simReducer` completely.
App's invariant needs only the first of them (Step 12a shows the difference),
but all of them are proved obligations, and the verdict would not be `VERIFIED` without them.
These rules are about each action and the state React applies it to. They do not say that
nothing moves on screen after a click on Pause (see "Not proven here").

**The proof file** *(Part 2)*: `proofs/model.lean` holds 8 lemmas about `openQty`, the total
quantity of the working orders: over a list (Step 10b), and over a Map after `set` and `delete`
(Step 13e). Lean checks them like the generated code, and the certificate's axioms are still the
three standard ones: the lemmas are proved, not assumed.

**Events, as modelled in `vreact/docs/SEMANTICS.md` §2**: discrete events (clicks) are checked
against the state the user saw. Timers are checked against any state. The App's clicks are also
checked against React's rebasing onto a pending timer update. A dispatched action is checked
where it is built, from the values its handler sees (Step 9). That this model matches React 18
is part of the trusted base below.

### The trusted base

What a reader has to trust, following `vreact/docs/SEMANTICS.md` §5:

* the **translation** from TypeScript to Lean and the **report** that reads Lean's output. Part
  2 relies on more of it: generic functions (a type parameter becomes a Lean type variable, an
  equality constraint `DecidableEq`, a field constraint a parameter that reads the field) and
  the check that a Map or a Set is only mutated as a fresh local copy;
* the **JavaScript runtime model** (that `findIndex`, `slice`, `%`, template strings … behave as
  modelled; since Part 2 also `Map` and `Set`: insertion order, `get` giving `undefined` for a
  missing key, `set` on a key in use keeping its place, modelled in vreact's Lean library as a
  list of entries) and the **React model** (React 18's batching, update queues, rebasing,
  reconciliation, event priorities). The check of a reducer's precondition at each `dispatch`
  rests on one fact of that model: React passes the dispatched action itself to every call of
  the reducer, also when it applies the queue again or calls the reducer twice in StrictMode
  (Step 9);
* Lean's kernel, plus the standard axioms. After the build, vreact checks every declaration of
  the generated modules and of the proof file again with the kernel, in a fresh process;
* **one argument on paper** *(Step 18)*: that no order id is given out twice in a run follows
  from two proved facts about one action of the reducer, by an induction over the actions that
  Lean does not check (Step 18b);
* **the proof file's whitelist** *(Part 2)*. `proofs/model.lean` is imported into the generated
  Lean, so it must not be able to change what the generated code means. vreact accepts only the
  listed kinds of commands in a proof file (theorems, definitions, simp and grind attributes,
  `grind_pattern`, a few options), rejects anything else (`axiom`, `instance`, `macro`, …)
  before Lean runs (Step 10b), and checks after the build that the proof module added only
  theorems, definitions and attributes. The lemmas themselves need no trust, since the kernel
  checked them; that the whitelist leaves nothing out does;
* outside the model: `main.tsx`, React itself, the DOM, the browser's anchor navigation (the
  "jump" scroll), the CSS (the heat colours and the watched rows' style are a stylesheet, not a
  proof), and when the timers actually fire.

### Not proven here

The probes linked below are changes to the final app that still verify (210/210, or 209/209
where the change removes an obligation; each run once, not part of the replay). Step 18 shows
how the outside review's findings were sorted into what a contract could close and what it
could not. A second review, of the final app, found more such gaps; they are stated here, each
with its probe, and the app was not changed for them.

* Which action, with which arguments, each control dispatches, and which cell a report comes
  from. The contracts check that every report is consistent and every dispatched action valid,
  not that it is the one the control stands for. Changes that verify: a cell that reports
  another cell's leg, side and price (snapshot 24); ▲ lowering the price
  ([probe](options-chain/probes/57-up-lowers-price/)); ☆ watching another strike, a "Collapse
  all" that collapses nothing and an "Expand all" that collapses every expiry
  ([probe](options-chain/probes/57-chain-wiring/)); and the one that matters most, a Submit
  that sends the opposite side and 1 lot, whatever the ticket shows
  ([probe](options-chain/probes/57-submit-sells/)): the ticket's title says "Buy" and its
  quantity 5, and a sell of 1 lot is placed. Step 18d explains why no contract can close this
  one: a callback contract cannot see the ticket's own state, and a reducer's precondition sees
  only the action. Which button dispatches Pause and which Rally is wiring too.
* Which operation the reducer runs for each action. `chainReducer`'s `switch` is plain code,
  and its contract says only that the invariant holds, that `nextId` does not go down and that
  new orders get fresh ids; the contracts of the operations apply only when the `switch` calls
  them. A `"cancel"` case that returns `u` verifies, and Cancel then does nothing
  ([probe](options-chain/probes/57-reducer-cancel-noop/)); so does a `"place"` case that places
  a 1-lot buy whatever side and quantity the action asks for
  ([probe](options-chain/probes/57-reducer-place-1-lot-buy/)). Unlike Submit's gap, this one a
  contract could state: a postcondition of `chainReducer` for each kind of action (for
  `"cancel"`: the order is gone and the others are kept). The final app has none, and it was not
  tried; the chain's handlers would see such postconditions too, as in Step 14b.
* That the ticket opens at the clicked price. `OrderTicket` copies `props.ticket.price` into its
  own state in plain code: `useState<int>(1)` there verifies, and every ticket then opens at
  0.05, whatever cell was clicked, and Submit places the order at that price unless it is
  changed ([probe](options-chain/probes/57-ticket-opens-at-1/)). As with Submit, no contract
  here reaches it: an invariant must hold after every click too, and the ticket's − and +
  change the price.
* That the screen shows the data. Rendering is proved not to fail, but what it shows is not
  specified: the numbers in the right columns and colours (also the in-the-money shading:
  `inTheMoney` has no contract), the ☆/★ glyph (Step 17b), the ticket's "Buy"/"Sell" title and
  its "Marketable" warning (`crosses` has no contract either: one that misses an order at
  exactly the bid or the ask verifies, [probe](options-chain/probes/57-marketable-strict/)), the
  "Pause feed"/"Resume feed" label. That includes which strike rows the chain renders:
  `shownRows`'s result is specified, but rendering every expiry's whole ladder verifies
  ([probe](options-chain/probes/57-rows-whole-ladder/)), and so do rows shown only for
  collapsed expiries and a window that ignores the held price
  ([probe](options-chain/probes/57-chain-wiring/)). It also includes the order of the working
  orders on screen: the chain renders `[...ui.orders]` in plain code, and a reversed list
  verifies ([probe](options-chain/probes/57-orders-reversed/)).
* That a filter button shows the rows its label names. `filterLabel` computes the label from
  `levelsOf` since Step 18c, so with this code the two agree, but no contract ties them:
  snapshot 53's table of labels in `filterLabel`, with a first filter of four rows, gives a "3"
  button that shows four rows, and verifies
  ([probe](options-chain/probes/57-label-3-shows-4/)). And the chain reads the window's size
  with `levelsOf(ui.filter)` in plain code: `levelsOf("s7")` there verifies, and every button
  then shows seven rows on each side ([probe](options-chain/probes/57-filter-ignored/)).
* That App passes the feed's offset to `moveFutures`, and that `moveFutures` leaves the rest of
  an expiry alone. The function is exact about the futures since Step 18, but its call in App's
  render is plain code: `moveFutures(EXPIRIES, offset * 10)` verifies
  ([probe](options-chain/probes/57-futures-call-site/)). And its contract says nothing about an
  expiry's label, symbol or strikes beyond `validChain`: a `moveFutures` that returns every
  expiry without strikes (`strikes: []`) verifies, and the chain then shows no strike rows at
  all ([probe](options-chain/probes/57-futures-no-strikes/)).
* That the functions the spec is written with are the intended ones. A function that a
  contract calls by name is part of the specification and is trusted as written (Steps 10 and
  12). Step 18 narrowed this. `accepts` is now tied to the invariant, so the rule it states is
  the invariant's, and the invariant is what has to be right, together with `withOrder`, the
  copy of `place`'s construction that the new claim is written with: a `withOrder` that files
  the order with one lot more lets the stricter cap of change 2 verify again
  ([probe](options-chain/probes/57-withorder-one-more/)). `stepFeed` now draws once and
  moves by the size of the draw, but the generator `nextSeed` and the walk's direction inside
  the band are still as written: a `nextSeed` that returns its argument draws the same number
  forever and verifies ([probe](options-chain/probes/57-seed-stuck/)). And the filter's numbers
  are a product decision: a first filter of 4 rows verifies, with "4" on its button
  ([probe](options-chain/probes/57-levels-changed/)).
* That `place` keeps the other orders in their relative order. Its contract says that the new
  order comes last, that every other order is still there unchanged, and that no other order
  appears (Step 18c), but not that the others keep their order: the full statement timed out in
  the chain's Submit handler (Step 14b).
* That `shownRows` keeps the ladder's order, that its rows are the ladder's own records, and
  that a watched strike the ladder does not list stays out. It does all three by construction
  (it is a `filter` of the ladder), and the run-time script of Step 19b checked the order, but
  its contract compares rows only by their strike and says none of this.
* That `amend` with a price below one tick leaves the order as it is. The code does, but the
  contract only says that the order stays valid and in its place, and that the others are
  unchanged.
* The initial states, beyond their invariants. The chain's `INITIAL_UI` and App's first `Sim`
  are constants that only the invariants check: a chain that starts with the All filter, the
  heat threshold at 5, an expiry focused and a strike watched, together with a feed that starts
  paused, with the rally on and the futures 2.00 above the data, verifies
  ([probe](options-chain/probes/57-initial-states/), both changes in one probe).
* That nothing moves on screen after a click on Pause. React applies a tick dispatched just
  before the click first, to a running feed, so the tick moves the futures; but React may
  render the Pause first and that tick after it (rebasing, `vreact/docs/SEMANTICS.md` §2.2).
  The futures then move once more while the button already says "Resume feed". `simReducer`'s
  rules are about each action and the state it is applied to, and that tick met a running
  feed. This follows from the model of React; no run of the verifier shows it.
* That the two intervals actually fire, or at which rate, or which action each one
  dispatches. The model lets timers fire at any time, in any order; "about 8 seconds" in Step
  12c is arithmetic, not a theorem. A 200 ms clock that dispatches `tick` instead of
  `rallyTick` verifies: Rally then changes only its button's label, and the random walk runs
  five times as often ([probe](options-chain/probes/57-rally-clock-ticks/)).
* That a nearest strike always exists for a non-empty ladder (true, but it needs induction; see
  below). The UI falls back to showing every strike if `atmIndex` ever returned −1.
* That the strikes are ascending. Nothing depends on it except the display order.
* That the ticket resets when another cell is clicked. This is done with a `key`, which is not
  verified.
* That the state forgets expiries and strikes that are no longer listed. The holds and the
  collapse flags of a delisted expiry stay in their Map and Set, and so do watched strikes that
  no expiry lists. Nothing reads the first two again; the watched strikes stay in the toolbar,
  where a click removes them. (As in Part 1, the state is not tied to the props: Step 4.)
* Anything about theoretical values, volatilities or the demo data, beyond `validChain`.
* Anything about saving the state: the working orders are lost on reload, and a
  `JSON.stringify` of the state would print its Maps and Sets as `{}`. The app does neither.
* Integer overflow: `int` is unbounded in the model. The values here are far below 2^53.

Two items of Part 1's list (Step 8) are proved now and have left it: the frames of `toggle`,
`setCollapsed`, `setFilter`, `jump` and `setHeat` (Step 14b), and the item about ids, in both
its parts: that `nextId` only grows (Step 14b), and that the id of a cancelled order is never
given to a new one (Step 18, with the last step, from one action to a whole run, argued by
hand). Step 18 also answered the outside review (18a): changes 1, 2 and 4 to 7 no longer verify,
and 18d gives the final status of all fourteen.

---

## Where the tool pushed back

Each item below is a limit of the tool (a quirk of synth, or a true statement the automation
could not prove) or a construct VTS rejected. In Part 1, each was resolved by restructuring the
code, and no `assume`, `@trusted` or Lean proof was added. Part 2 adds one proof file, for
facts about sums that need induction, and in one place (item 9) states less than it wanted to.
It adds no `assume` and no `@trusted` either. Step 18 adds no lemma: it states one claim in
other words (item 13) and replaces another with code that makes it unnecessary (item 14).

1. **`implies` in synth's random tests** (steps 02–03). Synth evaluates contracts as
   JavaScript, so `implies(r >= 0, nearest(ks, ks[r], price))` evaluates `ks[-1].strike` and
   throws. Every candidate then fails ("no candidate passed the tests"), even `-1`, which Lean
   proves. *Fix:* write guards that short-circuit in JavaScript too: `r < 0 || …`.
2. **Existence of a nearest strike** (step 06). "A non-empty ladder has a nearest strike" needs
   induction. *Fix:* the postcondition says "an ATM row is found whenever some strike is
   nearest". That excludes the `-1` escape hatch and is provable. The remaining gap is a plain
   mathematical fact, listed above under "Not proven here".
3. **Ternary of `int | null` and a narrowed `int`** (steps 13 and 13b): `type mismatch:
   expected int, got int | null`. *Fix:* annotate the const (`const center: int | null = …`).
4. **Sums need induction** (steps 29 and 40). Facts about a sum (`reduce`) after an append, a
   filter, a `Map.set` or a `Map.delete` hold for lists of every length, and the automation does
   not do induction. *Fix:* lemmas in `proofs/model.lean` (Steps 10b and 13e), the
   walkthrough's only hand-written Lean.
5. **A lemma's side condition that `grind` does not decide** (Step 13e,
   [probe](options-chain/probes/41-lemma-hypothesis/)). `openQty_set` with the hypothesis
   `k ∉ m.keys` was added to the goal, but `grind` did not decide the membership, and `place`'s
   invariant obligation still failed. *Fix:* state both cases, with an `if` on the membership;
   `grind` splits on it.
6. **A false postcondition that times out** (step 33). The random walk's arithmetic in the
   `"tick"` case uses up the budget, so the obligation fails as a timeout, not with a
   counterexample. The report then tries the goal's cases one at a time and shows the first
   that fails, the `"rallyTick"` case, with a counterexample. It stops there, so the `"tick"`
   case's own problem shows only in a probe with one case wrong at a time
   ([tick](options-chain/probes/33-tick-case-only/), [rally](options-chain/probes/33-rally-case-only/)).
   *Fix:* none needed: both cases were real bugs, fixed in the reducer (step 34). The same
   arithmetic made the false claim of step 55 about `stepFeed` time out (Step 18b): the frozen
   walk was caught, but as a timeout, not with a counterexample.
7. **Synth cannot delete from a Map or a Set** (step 39). Its candidates are expressions, and
   its Map and Set expressions only add (`new Map(m).set(k, v)`, `new Set(s).add(x)`): JS's
   `delete` returns a boolean, so a deletion is a statement, and the expression
   `new Map([...m].filter(([k]) => k !== id))` is not among synth's candidates. Synth's closing
   hint for a hole that involves a Map or a Set says so. *Fix:* `follow` and `cancel` by hand,
   copy then delete.
8. **Synth's search is close to its budget** (step 39): the candidate for `follow` is found
   after 45 to 50 s of the 60 s per hole.
9. **A timeout from a contract the caller does not need** (step 43). `place`'s
   `sameList([...r.orders.keys()], [...u.orders.keys(), u.nextId])` made the chain's Submit
   handler time out: the handler sees every postcondition of `place` through the reducer.
   Marking `chainReducer` `@opaque` moved the timeout into the reducer's own postcondition
   ([probe](options-chain/probes/43-opaque-reducer/)). *Fix:* the lighter
   `[...r.orders.keys()].indexOf(u.nextId) === u.orders.size`, which says less (see "Not proven
   here").
10. **Index parameters of `filter`** (Step 15a, [probe](options-chain/probes/45-filter-index/)):
    `e.strikes.filter((s, i) => …)` is rejected; only `map` takes an index. *Fix:* the window
    as a Set of strikes, and one `filter` over the ladder.
11. **A timeout on a false claim** (step 47). `sameList` over the keys after delete-then-set
    timed out instead of failing with a counterexample; the report's case-by-case diagnosis
    did not finish the case that replaces the order either. *Fix:* a narrower consequence
    (`indexOf(id)` unchanged) failed at once, with a counterexample that showed the bug
    (step 48).
12. **Totals that the Map lemmas do not cover** (steps 47 and 50). The cap after delete-then-set,
    and after re-sorting a Map's entries, is true but was not proved: `openQty_delete_le` is an
    inequality, and no lemma says that reordering keeps the total. Neither is in the final code,
    so no lemma was added.
13. **A fact several steps away** (steps 55 and 56). `chainReducer`'s claim that a new order's
    id is fresh timed out in its `"place"` case: it had to be inferred from `place`'s eight
    postconditions, with a split on `accepts`, and for an accepted order from the frame
    `keepsOrdersExcept`, order by order and field by field. Why the other ten cases, which have
    frames too, were proved and this one was not, was not isolated. *Fix:* state the fact the
    caller needs in the callee's contract, in the caller's words (`freshIds`, Step 18c); the
    case is then one step.
14. **The decimal text of a number** (steps 55 and 56). ``filterLabel(f) === `${r}` `` with `r`
    equal to 3 is true, but the automation does not evaluate Lean's `toString`, so it cannot see
    that the text of 3 is "3". *Fix:* compute the label from the number, so that there is
    nothing to prove (Step 18c). Four one-line lemmas would also have done.

Two more items were on this list when this walkthrough was first written, and the current
vreact no longer pushes back on either: synth offered `chainReducer` as a building block for
the very operations it calls, and gave up (steps 08–10, see 2b); and VTS rejected enum keys
(step 13, see Step 3).

Not on this list: the bracket ATM search of step 05. Its postconditions were not proved (they
were not checked, behind its failed index reads), and they are false: the search assumes an
ascending ladder that no contract promises, so there the verifier was right. Nor are the
surviving mutants of steps 24, 51 and 54: they are gaps in the spec, not in the tool, and Step
18d explains why some of them cannot be closed with VTS contracts. Nor are the
VTS rejections of steps 37 and 42. Those of step 37 (a reducer that mutates the state's Set, a
null test that is always true) each stopped a real bug. That of step 42 (`===` on values of an
unconstrained type parameter) stopped a contract whose JS meaning, "the same object", is not
what its proof would mean; for this reducer's frames the two happened to agree (Step 14a).
Nor is the rule that a reducer's `requires` may mention only the action (Step 9): it is what
makes the check at the dispatch sound, and the reason the cap is checked inside `place`
(Step 10). One behaviour is worth knowing, though it is not a limit: a failed `ensures` is
admitted as a whole, so a proof that used a true part of it rests on `sorry` too (Step 17a).
Splitting a conjunction into separate `ensures` shows which part the other proofs use.

---

## Try it yourself

```bash
bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain
cd examples/options-chain
npx vreact verify                 # ✔ VERIFIED 210/210, certificate on standard axioms
npx vreact synth src/model.ts     # nothing left to fill: "no hole<T>() in src/model.ts"
npx tsc --noEmit -p .             # clean
npm run dev                       # http://localhost:5173
```

Then break something and watch the verifier catch it. Each change below was made to the final
app and run once (a probe, not replayed; the probe's folder holds the changed file, the command
and the output):

| change | in | the verifier reports | probe |
|---|---|---|---|
| `onPick={(x) => props.onPick("put", "ask", x)}` on the put *bid* cell | `StrikeRow` | `[callback-contract]` | [probe](options-chain/probes/57-put-bid-reports-ask/) |
| `hi: Math.min(n, atm + levels)` | `strikeWindow` | `[postcondition]` (2) | [probe](options-chain/probes/57-window-off-by-one/) |
| `buy: t.side === "bid"` | `place` | `[postcondition]` | [probe](options-chain/probes/57-place-buys-on-bid/) |
| also file the order under the id below the next one, when it is free | `place` | `[postcondition]` (`freshIds`) | [probe](options-chain/probes/57-place-extra-order/) |
| `+ qty < MAX_OPEN` | `accepts` | `[postcondition]` of `place` (the cap is the invariant's) | [probe](options-chain/probes/57-cap-strict/) |
| `qty: qty - 1` in the Submit handler | `OptionsChain` | `[precondition]` of `chainReducer`, at the dispatch | [probe](options-chain/probes/57-dispatch-qty-minus-1/) |
| `focus: null` in `toggle`'s result | `toggle` | `[postcondition]` (its frame) | [probe](options-chain/probes/57-toggle-clears-focus/) |
| `[...ks.slice(span.lo, span.hi), ...ks.filter((s) => watch.has(s.strike))]` as the rows | `shownRows` | `[postcondition]` (each strike once) and `[unique-keys]` in the chain | [probe](options-chain/probes/57-rows-joined/) |
| the rally tick without `!s.rally \|\|` | `simReducer` | `[postcondition]` | [probe](options-chain/probes/57-rally-rule-missing/) |
| `return s;` for both toggles | `simReducer` | `[postcondition]` (2): the flags | [probe](options-chain/probes/57-pause-rally-noop/) |
| a rally tick with the rally off pauses the feed | `simReducer` | `[postcondition]` (the `paused` flag) | [probe](options-chain/probes/57-rally-tick-pauses/) |
| `shiftQuote(e.future, d * 10)` | `moveFutures` | `[postcondition]` | [probe](options-chain/probes/57-futures-times-ten/) |
| `f.offset` in both branches | `stepFeed` | `[postcondition]`, a timeout | [probe](options-chain/probes/57-walk-frozen/) |
| `orders.delete(id);` before the `set` | `amend` | `[postcondition]` (2): the cap, not proved; the list's order, a timeout | [probe](options-chain/probes/57-amend-delete-set/) |
| `setPrice(price - 1);` without its `if (price > 1)` on the price's "−" | `OrderTicket` | `[handler]` | [probe](options-chain/probes/57-ticket-unguarded/) |
| ▲ dispatching `price: o.price - 1` | `OptionsChain` | nothing: `✔ VERIFIED 210/210`, a surviving mutant | [probe](options-chain/probes/57-up-lowers-price/) |
| Submit sending `1` lot of the other side | `OrderTicket`, `OptionsChain` | nothing: `✔ VERIFIED 210/210` (Step 18d) | [probe](options-chain/probes/57-submit-sells/) |

And look for mutants that survive: each one is something the spec does not say. "Not proven
here" lists the known ones, and Step 18 shows how to sort them into those a contract can close
and those it cannot.

Replay the whole walkthrough. Each step's snapshot is copied into a temp project, the same
command is run (without `--write`), and the verdict and per-item statuses are compared with the
saved log:

```bash
bash docs/options-chain/replay.sh           # all steps (~46 minutes; steps 01-26: ~19, 27-57: ~27); non-zero on any mismatch
bash docs/options-chain/replay.sh 05 16     # just steps 05 and 16
bash docs/options-chain/replay.sh --stable docs/options-chain/26-final.txt   # the lines it compares
```

The synth steps run against the clock: each hole has a 60 s budget. In our runs, step 08 found
`holdAt` after 30 to 45 s, steps 09 and 10 found `cancel` after 34 to 40 s, and step 39 found
its candidate for `follow` after 45 to 50 s, depending on the machine's load. On a much slower
or busier machine such a fill may not be found in time, and the replay then reports a mismatch
for that step. The budget is wall-clock time, so keep the machine awake while the replay runs
(on macOS: `caffeinate -i bash docs/options-chain/replay.sh`).

The probes are not part of the replay. To re-run one, copy the snapshot of the step named in
its `base` file into a project the way the replay does, put the probe's `src/` or `proofs/`
files over it, and run the command in its `command` file. One probe is a script, not a
change: for `57-runtime-contracts`, put its `contracts.ts` next to `src/` in a project with the
app's npm dependencies (`npm ci`), and run its `command` in a shell.

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
| 20 TermRow, OrderTicket | `verify` (and `verify --full`) | ✗ handler (price → 0) | [src](options-chain/steps/20-children-bug/src/) | [log](options-chain/20-children-bug.txt), [full](options-chain/20-children-bug-full.txt) |
| 21 all children | `verify` | ✔ VERIFIED 122/122 | [src](options-chain/steps/21-children-verified/src/) | [log](options-chain/21-children-verified.txt) |
| 22 moving market | `verify` (and `verify --full`) | ✗ effect-robust | [src](options-chain/steps/22-app-stale-timer/src/) | [log](options-chain/22-app-stale-timer.txt), [full](options-chain/22-app-stale-timer-full.txt) |
| 23 the feed as one record | `verify` | ✔ VERIFIED 129/129 | [src](options-chain/steps/23-app-feed/src/) | [log](options-chain/23-app-feed.txt) |
| 24 three mutants | `verify` | ✔ VERIFIED 129/129: all three survive | [src](options-chain/steps/24-mutants/src/) | [log](options-chain/24-mutants.txt) |
| 25 stronger `place` contract | `verify` | ✗ the `place` mutant is caught (certificate still VERIFIED) | [src](options-chain/steps/25-mutants-place-spec/src/) | [log](options-chain/25-mutants-place-spec.txt) |
| 26 end of Part 1 | `verify` | ✔ VERIFIED 131/131 | [src](options-chain/steps/26-final/src/) | [log](options-chain/26-final.txt) |
| 27 action precondition, wrong quantity | `verify` (and `verify --full`) | ✗ precondition at the dispatch (qty 1 → 0) | [src](options-chain/steps/27-action-precondition-bug/src/), [proofs](options-chain/steps/27-action-precondition-bug/proofs/) | [log](options-chain/27-action-precondition-bug.txt), [full](options-chain/27-action-precondition-bug-full.txt) |
| 28 action precondition | `verify` | ✔ VERIFIED 142/142 | [src](options-chain/steps/28-action-precondition/src/), [proofs](options-chain/steps/28-action-precondition/proofs/) | [log](options-chain/28-action-precondition.txt) |
| 29 open-quantity cap, no lemmas | `verify` (and `verify --full`) | ✗ sums need induction (3 goals) | [src](options-chain/steps/29-open-cap-unproved/src/), [proofs](options-chain/steps/29-open-cap-unproved/proofs/) | [log](options-chain/29-open-cap-unproved.txt), [full](options-chain/29-open-cap-unproved-full.txt) |
| 30 cap with a proof file | `verify` | ✔ VERIFIED 142/142 | [src](options-chain/steps/30-open-cap/src/), [proofs](options-chain/steps/30-open-cap/proofs/) | [log](options-chain/30-open-cap.txt) |
| 31 Rally, limit on the snapshot | `verify` (and `verify --full`) | ✗ effect-robust (40 + 1 = 41) | [src](options-chain/steps/31-rally-snapshot-bug/src/), [proofs](options-chain/steps/31-rally-snapshot-bug/proofs/) | [log](options-chain/31-rally-snapshot-bug.txt), [full](options-chain/31-rally-snapshot-bug-full.txt) |
| 32 Rally | `verify` | ✔ VERIFIED 145/145 | [src](options-chain/steps/32-rally/src/), [proofs](options-chain/steps/32-rally/proofs/) | [log](options-chain/32-rally.txt) |
| 33 `simReducer` ignores `paused` | `verify` (and `verify --full`) | ✗ postcondition "paused: feed unchanged": a timeout, then the `"rallyTick"` case fails | [src](options-chain/steps/33-sim-paused-bug/src/), [proofs](options-chain/steps/33-sim-paused-bug/proofs/) | [log](options-chain/33-sim-paused-bug.txt), [full](options-chain/33-sim-paused-bug-full.txt) |
| 34 `simReducer` | `verify` | ✔ VERIFIED 148/148 | [src](options-chain/steps/34-sim-reducer/src/), [proofs](options-chain/steps/34-sim-reducer/proofs/) | [log](options-chain/34-sim-reducer.txt) |
| 35 clocks, rally rule missing | `verify` (and `verify --full`) | ✗ postcondition: a rally tick moves the feed with the rally off | [src](options-chain/steps/35-sim-clocks-bug/src/), [proofs](options-chain/steps/35-sim-clocks-bug/proofs/) | [log](options-chain/35-sim-clocks-bug.txt), [full](options-chain/35-sim-clocks-bug-full.txt) |
| 36 clocks | `verify` | ✔ VERIFIED 150/150 | [src](options-chain/steps/36-sim-clocks/src/), [proofs](options-chain/steps/36-sim-clocks/proofs/) | [log](options-chain/36-sim-clocks.txt) |
| 37 Maps and Sets, first draft | `verify` | ✗ VTS: mutation of the state's Set; `!== null` on a `get` is always true | [src](options-chain/steps/37-sets-maps-rejected/src/), [proofs](options-chain/steps/37-sets-maps-rejected/proofs/) | [log](options-chain/37-sets-maps-rejected.txt) |
| 38 synth on Maps | `synth src/reducer.ts` | `follow = { ...u, held: new Map() }`, `cancel = { ...u, orders: new Map() }`: weak specs | [src](options-chain/steps/38-reducer-synth-maps/src/), [proofs](options-chain/steps/38-reducer-synth-maps/proofs/) | [log](options-chain/38-reducer-synth-maps.txt) |
| 39 synth with frames | `synth src/reducer.ts` | `follow` via `jump`: tests pass, Lean rejects (`jump` has no frame); no deletion: by hand | [src](options-chain/steps/39-reducer-synth-frames/src/), [proofs](options-chain/steps/39-reducer-synth-frames/proofs/) | [log](options-chain/39-reducer-synth-frames.txt) |
| 40 ids from the size | `verify` | ✗ `Map.set` overwrites an order (`size + 1` in use); the cap needs Map lemmas | [src](options-chain/steps/40-place-overwrite/src/), [proofs](options-chain/steps/40-place-overwrite/proofs/) | [log](options-chain/40-place-overwrite.txt) |
| 41 reducer on Maps | `verify` | ✔ VERIFIED 150/150 | [src](options-chain/steps/41-reducer-maps-verified/src/), [proofs](options-chain/steps/41-reducer-maps-verified/proofs/) | [log](options-chain/41-reducer-maps-verified.txt) |
| 42 generic frames for records | `verify` | ✗ VTS: `===` on an unconstrained type parameter | [src](options-chain/steps/42-generic-records-rejected/src/), [proofs](options-chain/steps/42-generic-records-rejected/proofs/) | [log](options-chain/42-generic-records-rejected.txt) |
| 43 helpers and all frames | `verify` | ✗ timeout in the chain's Submit handler | [src](options-chain/steps/43-collections-timeout/src/), [proofs](options-chain/steps/43-collections-timeout/proofs/) | [log](options-chain/43-collections-timeout.txt) |
| 44 helpers, verified | `verify` (and `explain`) | ✔ VERIFIED 171/171 | [src](options-chain/steps/44-collections/src/), [proofs](options-chain/steps/44-collections/proofs/) | [log](options-chain/44-collections.txt), [explain](options-chain/44-collections-explain.txt) (also [reducer](options-chain/44-collections-explain-reducer.txt), [model](options-chain/44-collections-explain-model.txt)) |
| 45 watched strikes, two lists joined | `verify` (and `verify --full`) | ✗ unique-keys: a watched strike inside the window is rendered twice | [src](options-chain/steps/45-watch-dup-keys/src/), [proofs](options-chain/steps/45-watch-dup-keys/proofs/) | [log](options-chain/45-watch-dup-keys.txt), [full](options-chain/45-watch-dup-keys-full.txt) |
| 46 watched strikes | `verify` | ✔ VERIFIED 183/183 | [src](options-chain/steps/46-watch/src/), [proofs](options-chain/steps/46-watch/proofs/) | [log](options-chain/46-watch.txt) |
| 47 amend, delete then set | `verify` (and `verify --full`) | ✗ the cap is not proved; the list's order times out | [src](options-chain/steps/47-amend-timeout/src/), [proofs](options-chain/steps/47-amend-timeout/proofs/) | [log](options-chain/47-amend-timeout.txt), [full](options-chain/47-amend-timeout-full.txt) |
| 48 amend, a narrower claim | `verify` (and `verify --full`) | ✗ the amended order moves to the end (insertion order) | [src](options-chain/steps/48-amend-moves/src/), [proofs](options-chain/steps/48-amend-moves/proofs/) | [log](options-chain/48-amend-moves.txt), [full](options-chain/48-amend-moves-full.txt) |
| 49 amend with `set` | `verify` | ✔ VERIFIED 192/192 | [src](options-chain/steps/49-amend/src/), [proofs](options-chain/steps/49-amend/proofs/) | [log](options-chain/49-amend.txt) |
| 50 mutants caught | `verify` (and `verify --full`) | ✗ 3 mutants caught by the new frames | [src](options-chain/steps/50-mutants-caught/src/), [proofs](options-chain/steps/50-mutants-caught/proofs/) | [log](options-chain/50-mutants-caught.txt), [full](options-chain/50-mutants-caught-full.txt) |
| 51 mutants that survive | `verify` | ✔ VERIFIED 192/192: all four survive | [src](options-chain/steps/51-mutants-survive/src/), [proofs](options-chain/steps/51-mutants-survive/proofs/) | [log](options-chain/51-mutants-survive.txt) |
| 52 stronger spec | `verify` | ✗ 2 of the 4 mutants caught (frames by exception, `shownRows`) | [src](options-chain/steps/52-mutants-spec/src/), [proofs](options-chain/steps/52-mutants-spec/proofs/) | [log](options-chain/52-mutants-spec.txt) |
| 53 after the audit | `verify` | ✔ VERIFIED 195/195 | [src](options-chain/steps/53-audited/src/), [proofs](options-chain/steps/53-audited/proofs/) | [log](options-chain/53-audited.txt) |
| 54 the review's changes | `verify` | ✔ VERIFIED 195/195: all fourteen survive | [src](options-chain/steps/54-review-mutants/src/), [proofs](options-chain/steps/54-review-mutants/proofs/) | [log](options-chain/54-review-mutants.txt) |
| 55 stronger spec, changes in | `verify` (and `verify --full`) | ✗ changes 1, 2 and 4–7 caught; two claims not proved | [src](options-chain/steps/55-review-spec/src/), [proofs](options-chain/steps/55-review-spec/proofs/) | [log](options-chain/55-review-spec.txt), [full](options-chain/55-review-spec-full.txt) |
| 56 stronger spec | `verify` (and `verify --full`) | ✗ a timeout in the reducer; the decimal text of a number | [src](options-chain/steps/56-review-unproved/src/), [proofs](options-chain/steps/56-review-unproved/proofs/) | [log](options-chain/56-review-unproved.txt), [full](options-chain/56-review-unproved-full.txt) |
| 57 final | `verify` | ✔ VERIFIED 210/210 | [src](options-chain/steps/57-final-2/src/), [proofs](options-chain/steps/57-final-2/proofs/) | [log](options-chain/57-final-2.txt) |

The `--full` logs (steps 14, 20, 22, 27, 29, 31, 33, 35, 45, 47, 48, 50, 55 and 56) and the
three `explain` logs of step 44 are not part of the replay (it runs each step's command only).
Neither are the probes: runs of a step's snapshot with a change, quoted in the text. Each probe
folder in [`options-chain/probes/`](options-chain/probes/) has the changed file(s), a `base`
file naming the step it changes, the `command` and the `output.txt`:

| probe | base step | what it shows | where |
|---|---|---|---|
| [26-no-holes](options-chain/probes/26-no-holes/) | 26 | `synth` finds no hole in `model.ts` and `reducer.ts` | Step 8 |
| [28-requires-on-state](options-chain/probes/28-requires-on-state/) | 28 | a reducer's `requires` that mentions the state is rejected | Step 9 |
| [30-axiom-in-proof-file](options-chain/probes/30-axiom-in-proof-file/) | 30 | an `axiom` in a proof file is rejected | 10b |
| [30-failing-lemma](options-chain/probes/30-failing-lemma/) | 30 | a lemma whose proof fails | 10b |
| [33-tick-case-only](options-chain/probes/33-tick-case-only/) | 34 | only the `"tick"` case ignores `paused`: a timeout, and a `"tick"` case does not finish | 12a |
| [33-rally-case-only](options-chain/probes/33-rally-case-only/) | 34 | only the `"rallyTick"` case ignores `paused`: `grind` fails | 12a |
| [37-readonly-set](options-chain/probes/37-readonly-set/) | 37 | with `ReadonlySet`, TypeScript refuses the mutation | 13a |
| [41-lemma-hypothesis](options-chain/probes/41-lemma-hypothesis/) | 41 | `openQty_set` with a side condition instead of an `if` | 13e |
| [42-constrained-records](options-chain/probes/42-constrained-records/) | 42 | with the constraint, TypeScript refuses `sameEntries` on orders | 14a |
| [43-opaque-reducer](options-chain/probes/43-opaque-reducer/) | 43 | `chainReducer` `@opaque`: the timeout moves into the reducer | 14b |
| [45-filter-index](options-chain/probes/45-filter-index/) | 45 | `filter` with an index parameter is rejected | 15a |
| [50-toggle-alone](options-chain/probes/50-toggle-alone/) | 49 | the `toggle` mutant alone reaches the certificate | 17a |
| [50-toggle-split](options-chain/probes/50-toggle-split/) | 49 | the same, with the heat equality in its own `ensures` | 17a |
| [50-holdat-alone](options-chain/probes/50-holdat-alone/) | 49 | the `holdAt` mutant alone | 17a |
| [53-walk-frozen](options-chain/probes/53-walk-frozen/) | 53 | a `stepFeed` that keeps the offset: verifies | Step 12, 18a |
| [53-rules-changed](options-chain/probes/53-rules-changed/) | 53 | `levelsOf` and `accepts` changed: verifies | Step 10, 18a |
| [53-place-extra-order](options-chain/probes/53-place-extra-order/) | 53 | `place` also files the order under a cancelled id: verifies | 18a |
| [53-place-one-more](options-chain/probes/53-place-one-more/) | 53 | the reviewer's partial fix: one order more, 196/196 | 18a |
| [53-pause-rally-noop](options-chain/probes/53-pause-rally-noop/) | 53 | Pause and Rally do nothing: verifies | 18a |
| [53-rally-tick-pauses](options-chain/probes/53-rally-tick-pauses/) | 53 | a rally tick pauses the feed while the rally is off: verifies | 18a |
| [53-futures-times-ten](options-chain/probes/53-futures-times-ten/) | 53 | the futures moved ten times the offset: verifies | 18a |
| [53-submit-sells](options-chain/probes/53-submit-sells/) | 53 | Submit sends the opposite side and 1 lot: verifies | 18a |
| [53-chain-wiring](options-chain/probes/53-chain-wiring/) | 53 | four wiring and rendering changes in the chain: verify | 18a |
| [53-rows-whole-ladder](options-chain/probes/53-rows-whole-ladder/) | 53 | every expiry renders its whole ladder: verifies | 18a |
| [53-orders-reversed](options-chain/probes/53-orders-reversed/) | 53 | the working orders rendered newest first: verifies | 18a |
| [57-no-holes](options-chain/probes/57-no-holes/) | 57 | `synth` finds no hole in `model.ts` and `reducer.ts` | 19b |
| [57-runtime-contracts](options-chain/probes/57-runtime-contracts/) | 57 | a script that evaluates the contracts at run time; also its outputs on steps 47, 50, 51, 52 and 55 | 19b |
| [57-rally-tick-pauses](options-chain/probes/57-rally-tick-pauses/) | 57 | change 5 of the review alone: caught | 18b, Try it yourself |
| [57-place-extra-order](options-chain/probes/57-place-extra-order/) | 57 | change 1 of the review alone: caught by `freshIds` | 18c, Try it yourself |
| [57-levels-changed](options-chain/probes/57-levels-changed/) | 57 | a first filter of 4 rows, labelled "4": verifies | 18c, Not proven here |
| [57-submit-sells](options-chain/probes/57-submit-sells/) | 57 | Submit sends the opposite side and 1 lot: verifies | 18d, Not proven here |
| [57-chain-wiring](options-chain/probes/57-chain-wiring/) | 57 | four wiring and rendering changes in the chain: verify | 18d, Not proven here |
| [57-rows-whole-ladder](options-chain/probes/57-rows-whole-ladder/) | 57 | every expiry renders its whole ladder: verifies | 18d, Not proven here |
| [57-orders-reversed](options-chain/probes/57-orders-reversed/) | 57 | the working orders rendered newest first: verifies | 18d, Not proven here |
| [57-futures-call-site](options-chain/probes/57-futures-call-site/) | 57 | App passes ten times the offset to `moveFutures`: verifies | 18d, Not proven here |
| [57-seed-stuck](options-chain/probes/57-seed-stuck/) | 57 | a generator that never changes its seed: verifies, 209/209 | 18d, Not proven here |
| [57-withorder-one-more](options-chain/probes/57-withorder-one-more/) | 57 | `withOrder` files one lot more, with change 2: verifies | 18d, Not proven here |
| [57-label-3-shows-4](options-chain/probes/57-label-3-shows-4/) | 57 | snapshot 53's labels with change 3, a "3" button that shows four rows: verifies | 18c, Not proven here |
| [57-filter-ignored](options-chain/probes/57-filter-ignored/) | 57 | the chain's window always uses `levelsOf("s7")`: verifies | Not proven here |
| [57-reducer-cancel-noop](options-chain/probes/57-reducer-cancel-noop/) | 57 | the reducer's `"cancel"` case returns `u`: verifies | Not proven here |
| [57-reducer-place-1-lot-buy](options-chain/probes/57-reducer-place-1-lot-buy/) | 57 | the reducer's `"place"` case places a 1-lot buy: verifies | Not proven here |
| [57-ticket-opens-at-1](options-chain/probes/57-ticket-opens-at-1/) | 57 | the ticket opens at 0.05, whatever cell was clicked: verifies | Not proven here |
| [57-marketable-strict](options-chain/probes/57-marketable-strict/) | 57 | no "Marketable" warning at exactly the bid or the ask: verifies | Not proven here |
| [57-futures-no-strikes](options-chain/probes/57-futures-no-strikes/) | 57 | `moveFutures` drops every expiry's strikes: verifies | Not proven here |
| [57-initial-states](options-chain/probes/57-initial-states/) | 57 | other initial states of the chain and of the feed: verifies | Not proven here |
| [57-rally-clock-ticks](options-chain/probes/57-rally-clock-ticks/) | 57 | the 200 ms clock dispatches `tick`: verifies | Not proven here |
| `57-…` (fourteen more) | 57 | the other changes of "Try it yourself" | Try it yourself |
