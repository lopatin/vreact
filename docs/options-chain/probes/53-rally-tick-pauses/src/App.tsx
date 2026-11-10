// Root component: demo data for a hypothetical index futures contract "DIX" and the chain.
// Prices are ticks of 0.05; theoretical values were computed offline (Black-76) and are data.
import { useReducer, useEffect } from "react";
import { assert, ensures, implies, invariant, type int } from "vreact/spec";
import { type Expiry, type Quote, validChain } from "./model";
import { OptionsChain } from "./OptionsChain";

/** @opaque */
export const EXPIRIES: readonly Expiry[] = [
  {
    id: 1,
    symbol: "DIX",
    label: "DEC 26",
    future: { bid: 2048, bidQty: 62, ask: 2049, askQty: 56 },
    strikes: [
      { strike: 1920, call: { bid: 145, bidQty: 108, ask: 153, askQty: 83 }, put: { bid: null, bidQty: 0, ask: 16, askQty: 154 }, callTheo: 146, putTheo: 18, vol: 2286 },
      { strike: 1940, call: { bid: 127, bidQty: 43, ask: 135, askQty: 20 }, put: { bid: 24, bidQty: 72, ask: 28, askQty: 47 }, callTheo: 130, putTheo: 22, vol: 2253 },
      { strike: 1960, call: { bid: 113, bidQty: 149, ask: 119, askQty: 125 }, put: { bid: 23, bidQty: 13, ask: 27, askQty: 45 }, callTheo: 115, putTheo: 27, vol: 2221 },
      { strike: 1980, call: { bid: 98, bidQty: 82, ask: 104, askQty: 5 }, put: { bid: 32, bidQty: 110, ask: 36, askQty: 133 }, callTheo: 101, putTheo: 33, vol: 2191 },
      { strike: 2000, call: { bid: 86, bidQty: 69, ask: 92, askQty: 142 }, put: { bid: 36, bidQty: 7, ask: 40, askQty: 78 }, callTheo: 87, putTheo: 39, vol: 2163 },
      { strike: 2020, call: { bid: 70, bidQty: 41, ask: 76, askQty: 53 }, put: { bid: 46, bidQty: 126, ask: 52, askQty: 96 }, callTheo: 75, putTheo: 47, vol: 2136 },
      { strike: 2040, call: { bid: 59, bidQty: 16, ask: 65, askQty: 140 }, put: { bid: 55, bidQty: 38, ask: 61, askQty: 68 }, callTheo: 64, putTheo: 56, vol: 2110 },
      { strike: 2060, call: { bid: 45, bidQty: 58, ask: 51, askQty: 86 }, put: { bid: 63, bidQty: 58, ask: 69, askQty: 99 }, callTheo: 53, putTheo: 65, vol: 2086 },
      { strike: 2080, call: { bid: 40, bidQty: 69, ask: 46, askQty: 129 }, put: { bid: 73, bidQty: 119, ask: 79, askQty: 99 }, callTheo: 44, putTheo: 76, vol: 2063 },
      { strike: 2100, call: { bid: 33, bidQty: 6, ask: 37, askQty: 54 }, put: { bid: 86, bidQty: 128, ask: 92, askQty: 94 }, callTheo: 36, putTheo: 88, vol: 2041 },
      { strike: 2120, call: { bid: 28, bidQty: 94, ask: 32, askQty: 23 }, put: { bid: 98, bidQty: 74, ask: 104, askQty: 122 }, callTheo: 29, putTheo: 101, vol: 2021 },
      { strike: 2140, call: { bid: 22, bidQty: 24, ask: 26, askQty: 73 }, put: { bid: 111, bidQty: 111, ask: 117, askQty: 81 }, callTheo: 23, putTheo: 115, vol: 2002 },
      { strike: 2160, call: { bid: 13, bidQty: 72, ask: 17, askQty: 147 }, put: { bid: 128, bidQty: 96, ask: 136, askQty: 98 }, callTheo: 18, putTheo: 130, vol: 1984 },
      { strike: 2180, call: { bid: null, bidQty: 0, ask: 16, askQty: 37 }, put: { bid: 142, bidQty: 100, ask: 150, askQty: 39 }, callTheo: 14, putTheo: 146, vol: 1967 },
    ],
  },
  {
    id: 2,
    symbol: "DIX",
    label: "MAR 27",
    future: { bid: 2062, bidQty: 73, ask: 2063, askQty: 35 },
    strikes: [
      { strike: 1920, call: { bid: 194, bidQty: 14, ask: 202, askQty: 86 }, put: { bid: 53, bidQty: 119, ask: 59, askQty: 145 }, callTheo: 197, putTheo: 55, vol: 2309 },
      { strike: 1940, call: { bid: 174, bidQty: 32, ask: 182, askQty: 72 }, put: { bid: 56, bidQty: 13, ask: 62, askQty: 34 }, callTheo: 182, putTheo: 60, vol: 2275 },
      { strike: 1960, call: { bid: 163, bidQty: 6, ask: 171, askQty: 136 }, put: { bid: 61, bidQty: 121, ask: 67, askQty: 52 }, callTheo: 168, putTheo: 66, vol: 2242 },
      { strike: 1980, call: { bid: 149, bidQty: 108, ask: 157, askQty: 113 }, put: { bid: 69, bidQty: 95, ask: 75, askQty: 123 }, callTheo: 154, putTheo: 72, vol: 2211 },
      { strike: 2000, call: { bid: 136, bidQty: 15, ask: 144, askQty: 138 }, put: { bid: 78, bidQty: 128, ask: 84, askQty: 130 }, callTheo: 141, putTheo: 79, vol: 2182 },
      { strike: 2020, call: { bid: 124, bidQty: 65, ask: 132, askQty: 10 }, put: { bid: 85, bidQty: 131, ask: 91, askQty: 106 }, callTheo: 129, putTheo: 87, vol: 2154 },
      { strike: 2040, call: { bid: 114, bidQty: 89, ask: 120, askQty: 51 }, put: { bid: 87, bidQty: 32, ask: 93, askQty: 110 }, callTheo: 117, putTheo: 95, vol: 2128 },
      { strike: 2060, call: { bid: 101, bidQty: 24, ask: 107, askQty: 31 }, put: { bid: 99, bidQty: 117, ask: 105, askQty: 57 }, callTheo: 106, putTheo: 104, vol: 2102 },
      { strike: 2080, call: { bid: 93, bidQty: 98, ask: 99, askQty: 128 }, put: { bid: 109, bidQty: 11, ask: 115, askQty: 10 }, callTheo: 96, putTheo: 114, vol: 2079 },
      { strike: 2100, call: { bid: 81, bidQty: 116, ask: 87, askQty: 108 }, put: { bid: 117, bidQty: 67, ask: 125, askQty: 113 }, callTheo: 86, putTheo: 124, vol: 2056 },
      { strike: 2120, call: { bid: 75, bidQty: 71, ask: 81, askQty: 136 }, put: { bid: 129, bidQty: 150, ask: 137, askQty: 83 }, callTheo: 77, putTheo: 135, vol: 2035 },
      { strike: 2140, call: { bid: 66, bidQty: 110, ask: 72, askQty: 148 }, put: { bid: 139, bidQty: 50, ask: 147, askQty: 57 }, callTheo: 68, putTheo: 146, vol: 2015 },
      { strike: 2160, call: { bid: 56, bidQty: 44, ask: 62, askQty: 91 }, put: { bid: 154, bidQty: 73, ask: 162, askQty: 20 }, callTheo: 61, putTheo: 159, vol: 1997 },
      { strike: 2180, call: { bid: 53, bidQty: 12, ask: 59, askQty: 134 }, put: { bid: 170, bidQty: 64, ask: 178, askQty: 19 }, callTheo: 53, putTheo: 171, vol: 1979 },
    ],
  },
  {
    id: 3,
    symbol: "DIX",
    label: "JUN 27",
    future: { bid: 2077, bidQty: 91, ask: 2078, askQty: 66 },
    strikes: [
      { strike: 1920, call: { bid: 236, bidQty: 69, ask: 244, askQty: 146 }, put: { bid: 78, bidQty: 100, ask: 84, askQty: 150 }, callTheo: 238, putTheo: 81, vol: 2334 },
      { strike: 1940, call: { bid: 216, bidQty: 18, ask: 224, askQty: 144 }, put: { bid: 83, bidQty: 106, ask: 89, askQty: 89 }, callTheo: 223, putTheo: 86, vol: 2299 },
      { strike: 1960, call: { bid: 203, bidQty: 92, ask: 211, askQty: 97 }, put: { bid: 93, bidQty: 148, ask: 99, askQty: 25 }, callTheo: 209, putTheo: 92, vol: 2265 },
      { strike: 1980, call: { bid: 194, bidQty: 25, ask: 202, askQty: 133 }, put: { bid: 93, bidQty: 50, ask: 99, askQty: 85 }, callTheo: 196, putTheo: 99, vol: 2233 },
      { strike: 2000, call: { bid: 179, bidQty: 51, ask: 187, askQty: 67 }, put: { bid: 100, bidQty: 43, ask: 106, askQty: 114 }, callTheo: 183, putTheo: 106, vol: 2203 },
      { strike: 2020, call: { bid: 167, bidQty: 49, ask: 175, askQty: 46 }, put: { bid: 109, bidQty: 42, ask: 115, askQty: 150 }, callTheo: 170, putTheo: 113, vol: 2174 },
      { strike: 2040, call: { bid: 154, bidQty: 99, ask: 162, askQty: 59 }, put: { bid: 118, bidQty: 105, ask: 126, askQty: 24 }, callTheo: 158, putTheo: 121, vol: 2147 },
      { strike: 2060, call: { bid: 141, bidQty: 127, ask: 149, askQty: 21 }, put: { bid: 127, bidQty: 19, ask: 135, askQty: 151 }, callTheo: 146, putTheo: 129, vol: 2121 },
      { strike: 2080, call: { bid: 131, bidQty: 56, ask: 139, askQty: 58 }, put: { bid: 134, bidQty: 126, ask: 142, askQty: 11 }, callTheo: 135, putTheo: 138, vol: 2096 },
      { strike: 2100, call: { bid: 119, bidQty: 116, ask: 127, askQty: 55 }, put: { bid: 147, bidQty: 100, ask: 155, askQty: 141 }, callTheo: 125, putTheo: 148, vol: 2073 },
      { strike: 2120, call: { bid: 115, bidQty: 29, ask: 121, askQty: 12 }, put: { bid: 152, bidQty: 16, ask: 160, askQty: 120 }, callTheo: 115, putTheo: 158, vol: 2051 },
      { strike: 2140, call: { bid: 105, bidQty: 123, ask: 111, askQty: 137 }, put: { bid: 163, bidQty: 122, ask: 171, askQty: 48 }, callTheo: 105, putTheo: 168, vol: 2031 },
      { strike: 2160, call: { bid: 94, bidQty: 67, ask: 100, askQty: 6 }, put: { bid: 176, bidQty: 106, ask: 184, askQty: 119 }, callTheo: 96, putTheo: 179, vol: 2011 },
      { strike: 2180, call: { bid: 85, bidQty: 90, ask: 91, askQty: 135 }, put: { bid: 186, bidQty: 149, ask: 194, askQty: 129 }, callTheo: 88, putTheo: 191, vol: 1993 },
    ],
  },
];
// a fact about the constant, proved once by evaluation and then available to every proof
assert(validChain(EXPIRIES));

/** The simulated futures stay within ±MAX_MOVE ticks (±2.00) of the data. */
export const MAX_MOVE: int = 40;

/** Shift a market by d ticks (a missing side stays missing). */
export function shiftQuote(q: Quote, d: int): Quote {
  return { ...q, bid: q.bid === null ? null : q.bid + d, ask: q.ask === null ? null : q.ask + d };
}

/** The demo feed: every expiry's futures market moved by d ticks. */
export function moveFutures(es: readonly Expiry[], d: int): readonly Expiry[] {
  ensures((r: readonly Expiry[]) => implies(validChain(es), validChain(r)));
  return es.map((e) => ({ ...e, future: shiftQuote(e.future, d) }));
}

/** A small linear congruential generator for the simulated market. */
export function nextSeed(s: int): int {
  return (s * 75 + 74) % 65537;
}

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

/** The simulation: the feed, and the two controls that drive it. One record, one reducer. */
export type Sim = { readonly feed: Feed; readonly paused: boolean; readonly rally: boolean };

export type SimAction =
  | { readonly kind: "tick" } // the 0.8 s random walk
  | { readonly kind: "rallyTick" } // the 0.2 s climb
  | { readonly kind: "togglePause" }
  | { readonly kind: "toggleRally" };

/** The feed is exactly the same. */
export function sameFeed(a: Feed, b: Feed): boolean {
  return a.offset === b.offset && a.seed === b.seed;
}

/** Every change to the simulation goes through here, so its contract holds for every update. */
export function simReducer(s: Sim, a: SimAction): Sim {
  ensures((r: Sim) => implies(validFeed(s.feed), validFeed(r.feed)));
  // while paused, nothing moves the feed
  ensures((r: Sim) => implies(s.paused, sameFeed(r.feed, s.feed)));
  // ... and while running, a tick is one step of the random walk (so "never move" is not a fix)
  ensures((r: Sim) => implies(!s.paused && a.kind === "tick", sameFeed(r.feed, stepFeed(s.feed))));
  // a rally tick moves the feed only while a rally is on ...
  ensures((r: Sim) => implies(a.kind === "rallyTick" && !s.rally, sameFeed(r.feed, s.feed)));
  // ... and then it climbs one tick, up to the top of the band
  ensures((r: Sim) =>
    implies(a.kind === "rallyTick" && s.rally && !s.paused && s.feed.offset < MAX_MOVE, r.feed.offset === s.feed.offset + 1),
  );
  // The rules live only here, checked on the state the action is applied to: App's intervals
  // tick unconditionally, and a tick may arrive after a pause or after the rally is stopped.
  switch (a.kind) {
    case "tick":
      return s.paused ? s : { ...s, feed: stepFeed(s.feed) };
    case "rallyTick":
      return !s.rally ? { ...s, paused: true } : s.paused || s.feed.offset >= MAX_MOVE ? s : { ...s, feed: { ...s.feed, offset: s.feed.offset + 1 } };
    case "togglePause":
      return { ...s, paused: !s.paused };
    case "toggleRally":
      return { ...s, rally: !s.rally };
  }
}

export function App() {
  const [sim, dispatch] = useReducer(simReducer, { feed: { offset: 0, seed: 1 }, paused: false, rally: false });
  invariant(validFeed(sim.feed));
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
  const feed = sim.feed;
  const offset = feed.offset;
  const expiries = moveFutures(EXPIRIES, offset);
  return (
    <div className="app">
      <header>
        <h1>Options chain</h1>
        <p className="muted">
          Hypothetical DIX index futures options · demo data · prices in ticks of 0.05 · simulated futures move{" "}
          {offset >= 0 ? "+" : ""}
          {offset} ticks
        </p>
        <button onClick={() => dispatch({ kind: "togglePause" })}>{sim.paused ? "Resume feed" : "Pause feed"}</button>
        <button onClick={() => dispatch({ kind: "toggleRally" })}>{sim.rally ? "Stop rally" : "Rally"}</button>
      </header>
      <OptionsChain expiries={expiries} />
    </div>
  );
}
