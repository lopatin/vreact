// Options-chain model: market data, the strike ladder, the heat map and orders.
//
// Prices are integer ticks (`int`), never `number`: a `number` is an IEEE double, and the
// prover cannot reason about its values. Exchange prices are tick-based anyway: the demo
// uses a tick of 0.05, so 102.40 is 2048 ticks. A missing price is `null`.
//
// Theoretical values and volatilities are *input data* (no pricing model is verified here).
import { requires, ensures, implies, distinct, forall, idiv, type int } from "vreact/spec";
import { byId } from "./collections";

export type Right = "call" | "put";
/** A side of a market: the best bid (buyers) or the best ask (sellers). */
export type Side = "bid" | "ask";

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

/**
 * One expiry: its futures market (the underlying) and its strike ladder (ascending, for
 * display: no proof relies on the order).
 */
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

/** The call or the put market of a strike. */
export function legOf(s: Strike, right: Right): Quote {
  return right === "call" ? s.call : s.put;
}

/** The theoretical value of the call or the put. */
export function theoOf(s: Strike, right: Right): int {
  return right === "call" ? s.callTheo : s.putTheo;
}

/** The price shown in a bid or an ask cell. */
export function quotePrice(q: Quote, side: Side): int | null {
  ensures((r: int | null) => r === (side === "bid" ? q.bid : q.ask));
  switch (side) {
    case "bid":
      return q.bid;
    case "ask":
      return q.ask;
  }
}

/** The bid <= r <= ask part of midPrice's contract (when the market is two-sided and not crossed). */
export function withinSpread(q: Quote, r: int | null): boolean {
  const b = q.bid;
  const a = q.ask;
  if (b === null || a === null || b > a) return true;
  return r !== null && b <= r && r <= a;
}

/** r is the mid of a two-sided market, rounded down (true for a one-sided market). */
export function isMid(q: Quote, r: int | null): boolean {
  const b = q.bid;
  const a = q.ask;
  if (b === null || a === null) return true;
  return r === idiv(b + a, 2);
}

/** Reference price of a market: the mid (rounded down) if two-sided, else the side present, else null. */
export function midPrice(q: Quote): int | null {
  ensures((r: int | null) => isMid(q, r));
  ensures((r: int | null) => q.ask !== null || r === q.bid);
  ensures((r: int | null) => q.bid !== null || r === q.ask);
  ensures((r: int | null) => withinSpread(q, r));
  const b = q.bid;
  const a = q.ask;
  if (b !== null && a !== null) return idiv(b + a, 2);
  if (b !== null) return b;
  return a;
}

/** A call is in the money when its strike is below the price, a put when it is above. */
export function inTheMoney(right: Right, strike: int, price: int): boolean {
  return right === "call" ? strike < price : strike > price;
}

export function dist(a: int, b: int): int {
  return a >= b ? a - b : b - a;
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
  // `r < 0 || …`, not `implies(r >= 0, …)`: synth runs contracts as JavaScript, where
  // implies(a, b) is a call that evaluates b (here ks[-1].strike) even when a is false
  ensures((r: int) => r < 0 || nearest(ks, ks[r], price));
  // "-1 for none" must not be an escape hatch: whenever some strike is nearest, an ATM row is
  // found. (A non-empty ladder always has one; the prover cannot show that without induction.)
  ensures((r: int) => implies(ks.some((s) => nearest(ks, s, price)), r >= 0));
  // the first strike that no other strike beats (O(n²) on a ladder of ~15 strikes)
  return ks.findIndex((s) => nearest(ks, s, price));
}

/** Rows [lo, hi) of a ladder. */
export type Span = { readonly lo: int; readonly hi: int };

/** The quick strike filter: row i is shown when it is at most `levels` rows from the ATM row. */
export function inWindow(i: int, atm: int, levels: int): boolean {
  return atm - levels <= i && i <= atm + levels;
}

/** The rows of a ladder of n strikes that the filter shows around the ATM row. */
export function strikeWindow(n: int, atm: int, levels: int): Span {
  requires(0 <= atm && atm < n && levels >= 0);
  ensures((r: Span) => 0 <= r.lo && r.lo <= atm && atm < r.hi && r.hi <= n);
  ensures((r: Span) => forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, levels)));
  return { lo: Math.max(0, atm - levels), hi: Math.min(n, atm + levels + 1) };
}

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
  return ks.filter((s) => win.has(s.strike) || watch.has(s.strike));
}

/** Quick strike filter: 3, 7, 11 or 99 strikes above and below the price, or all strikes. */
export type StrikeFilter = "s3" | "s7" | "s11" | "s99" | "all";

/** A filter button's label: the number of rows it shows on each side, so the two cannot disagree. */
export function filterLabel(f: StrikeFilter): string {
  switch (f) {
    case "s3":
      return "3";
    case "s7":
      return "7";
    case "s11":
      return "11";
    case "s99":
      return "99";
    case "all":
      return "All";
  }
}

export function levelsOf(f: StrikeFilter): int | null {
  ensures((r: int | null) => r === null || r >= 1);
  switch (f) {
    case "s3":
      return 4;
    case "s7":
      return 7;
    case "s11":
      return 11;
    case "s99":
      return 99;
    case "all":
      return null;
  }
}

/** Heat of a bid/ask cell: how close the theoretical value is to crossing the market. */
export type Heat = "none" | "near" | "cross" | "deep";

/** By how many ticks the theoretical value has crossed the price of a cell (> 0: crossed). */
export function edge(side: Side, price: int, theo: int): int {
  return side === "bid" ? price - theo : theo - price;
}

/**
 * Heat map with a threshold of t ticks: "near" when the theoretical value is within t ticks of
 * the price without crossing it, "cross" when it crosses by 1..t ticks, "deep" when by more.
 */
export function heatOf(side: Side, price: int | null, theo: int, t: int): Heat {
  requires(t >= 1);
  ensures((r: Heat) => price !== null || r === "none");
  ensures((r: Heat) => price === null || (r === "deep") === edge(side, price, theo) > t);
  ensures((r: Heat) => price === null || (r === "cross") === (0 < edge(side, price, theo) && edge(side, price, theo) <= t));
  ensures((r: Heat) => price === null || (r === "near") === (-t <= edge(side, price, theo) && edge(side, price, theo) <= 0));
  if (price === null) return "none";
  const d = edge(side, price, theo);
  if (d > t) return "deep";
  if (d > 0) return "cross";
  if (d >= -t) return "near";
  return "none";
}

/** What a price cell trades: the expiry's futures contract, or its call or put at a strike. */
export type Leg = "future" | "call" | "put";

export function legFor(right: Right): Leg {
  return right === "call" ? "call" : "put";
}

/** The label of an expiry ("?" when it is not listed). */
export function labelOf(es: readonly Expiry[], id: int): string {
  const e = byId(es, id);
  return e === undefined ? "?" : `${e.symbol} ${e.label}`;
}

/** A clicked bid/ask cell: the contract, the side of the market and the price it showed. */
export type Ticket = {
  readonly expiry: int;
  readonly leg: Leg;
  readonly strike: int; // 0 for the future
  readonly side: Side;
  readonly price: int;
};

/** The live market of a ticket's contract in its expiry (null when the strike is not listed). */
export function marketOf(e: Expiry, t: Ticket): Quote | null {
  if (t.leg === "future") return e.future;
  const s = e.strikes.find((x) => x.strike === t.strike);
  if (s === undefined) return null;
  return t.leg === "call" ? s.call : s.put;
}

/**
 * A working order. Clicking a bid prepares a sell (hit the bid), an ask a buy (lift the offer).
 * It has no id field: the working orders are a Map from id to order, and the key is the id.
 */
export type Order = {
  readonly expiry: int;
  readonly leg: Leg;
  readonly strike: int;
  readonly buy: boolean;
  readonly qty: int;
  readonly price: int;
};

export const MAX_QTY: int = 500;

export function validQty(q: int): boolean {
  return 1 <= q && q <= MAX_QTY;
}

/** Order validation: a quantity of 1..MAX_QTY lots at a positive price. */
export function validOrder(o: Order): boolean {
  return validQty(o.qty) && o.price > 0;
}

export const MAX_OPEN: int = 1000;

/** Total quantity of the working orders. @opaque */
export function openQty(os: readonly Order[]): int {
  return os.reduce((n, o) => n + o.qty, 0);
}

/** A price in ticks of 0.05 as text, e.g. 2048 → "102.40". */
export function fmtPrice(t: int): string {
  const c = t * 5;
  const whole = idiv(c, 100);
  const frac = c - whole * 100;
  return `${whole}.${frac < 10 ? "0" : ""}${frac}`;
}

/** A contract as text: "FUT", "102.00 C" or "102.00 P". */
export function contractText(leg: Leg, strike: int): string {
  switch (leg) {
    case "future":
      return "FUT";
    case "call":
      return `${fmtPrice(strike)} C`;
    case "put":
      return `${fmtPrice(strike)} P`;
  }
}

/** A market as "bid / ask", with "–" for a missing side. */
export function quoteText(q: Quote): string {
  const b = q.bid;
  const a = q.ask;
  return `${b === null ? "–" : fmtPrice(b)} / ${a === null ? "–" : fmtPrice(a)}`;
}

/** A buy at or above the ask, or a sell at or below the bid, trades at once. */
export function crosses(buy: boolean, price: int, q: Quote): boolean {
  const b = q.bid;
  const a = q.ask;
  if (buy) return a !== null && price >= a;
  return b !== null && price <= b;
}

/** A volatility in basis points as a percentage, e.g. 2163 → "21.6%". */
export function fmtVol(bp: int): string {
  return `${idiv(bp, 100)}.${idiv(bp - idiv(bp, 100) * 100, 10)}%`;
}
