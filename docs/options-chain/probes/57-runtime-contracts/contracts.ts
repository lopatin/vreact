// The contracts at run time (walkthrough, Step 19b): the app's logic with real JS Maps and Sets.
// Random action sequences through chainReducer, and every operation on random (also unreachable)
// states, checking each function's own `ensures` (recorded by vreact/spec in test mode) on the
// result; then the same for the simulated feed of App.tsx (simReducer, stepFeed, moveFutures).
// Run it from a project whose src/ is a snapshot, with the app's npm dependencies:
//   npx esbuild contracts.ts --bundle --platform=node --format=esm --outfile=contracts.mjs && node contracts.mjs src
import * as R from "./src/reducer";
import * as M from "./src/model";
import * as C from "./src/collections";
import * as A from "./src/App";
import { EXPIRIES } from "./src/App";
import { readFileSync } from "node:fs";
const SRC = process.argv[2] ?? "src";
const srcReducer = readFileSync(SRC + "/reducer.ts", "utf8");
const srcModel = readFileSync(SRC + "/model.ts", "utf8");
const srcCollections = readFileSync(SRC + "/collections.ts", "utf8");
const srcApp = readFileSync(SRC + "/App.tsx", "utf8");

type Post = (r: unknown) => boolean;
const T: { posts: Post[] } = { posts: [] };
// vreact/spec's test hook (the key `vreact synth` uses; the runtime reads no string-named global)
(globalThis as any)[Symbol.for("vreact.spec.test")] = T;

/** number of `ensures(` at the top of `export function name(` in a source file */
function ownEnsures(src: string, name: string): number {
  const m = new RegExp(`export function ${name}[<(]`).exec(src);
  const i = m ? m.index : -1;
  if (i < 0) throw new Error("no function " + name);
  const body = src.slice(i);
  const end = body.indexOf("\n}\n");
  return (body.slice(0, end).match(/\n  ensures\(/g) ?? []).length;
}

let checked = 0;
const fails = new Map<string, number>();
function call<A extends unknown[], Res>(name: string, src: string, f: (...a: A) => Res, ...args: A): Res {
  T.posts = [];
  const r = f(...args);
  const k = ownEnsures(src, name);
  const mine = T.posts.slice(0, k);
  mine.forEach((p, j) => {
    checked++;
    if (!p(r)) {
      const key = `${name} post ${j + 1}`;
      fails.set(key, (fails.get(key) ?? 0) + 1);
      if ((fails.get(key) ?? 0) <= 2) console.log("FAIL", key, JSON.stringify(args, replacer).slice(0, 400));
    }
  });
  return r;
}
function replacer(_k: string, v: unknown) {
  if (v instanceof Map) return { Map: [...v] };
  if (v instanceof Set) return { Set: [...v] };
  return v;
}

// mulberry32, in 32-bit integer arithmetic. (An earlier version computed an LCG in floating
// point: the product lost its low bits, so rnd(n) for an even n always gave the same parity.)
let seed = 12345;
const rnd = (n: number) => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) % n;
};
const pick = <X,>(xs: readonly X[]): X => xs[rnd(xs.length)];
const FILTERS: M.StrikeFilter[] = ["s3", "s7", "s11", "s99", "all"];
const IDS = [1, 2, 3, 4];
const STRIKES = EXPIRIES[0].strikes.map((s) => s.strike);

function randomTicket(): M.Ticket {
  const e = pick(EXPIRIES);
  const leg = pick<M.Leg>(["future", "call", "put"]);
  return { expiry: e.id, leg, strike: leg === "future" ? 0 : pick(STRIKES), side: pick<M.Side>(["bid", "ask"]), price: 1 + rnd(300) };
}

function randomAction(u: R.ChainUi): R.Action {
  const orderIds = [...u.orders.keys()];
  switch (rnd(11)) {
    case 0: return { kind: "toggle", expiry: pick(IDS) };
    case 1: return { kind: "collapse", ids: IDS.filter(() => rnd(2) === 0) };
    case 2: return { kind: "filter", filter: pick(FILTERS) };
    case 3: return { kind: "watch", strike: pick(STRIKES) };
    case 4: return { kind: "hold", expiry: pick(IDS), price: 1900 + rnd(300) };
    case 5: return { kind: "follow", expiry: pick(IDS) };
    case 6: return { kind: "jump", expiry: pick(IDS) };
    case 7: return { kind: "heat", ticks: rnd(8) - 1 };
    case 8: return { kind: "place", ticket: randomTicket(), qty: 1 + rnd(M.MAX_QTY), price: rnd(200) - 5 };
    case 9: return { kind: "amend", id: orderIds.length && rnd(4) ? pick(orderIds) : 99, price: rnd(200) - 5 };
    default: return { kind: "cancel", id: orderIds.length && rnd(4) ? pick(orderIds) : 99 };
  }
}

/** each operation called directly, checking its own contract */
function applyChecked(u: R.ChainUi, a: R.Action): R.ChainUi {
  switch (a.kind) {
    case "toggle": call("toggle", srcReducer, R.toggle, u, a.expiry); break;
    case "collapse": call("setCollapsed", srcReducer, R.setCollapsed, u, a.ids); break;
    case "filter": call("setFilter", srcReducer, R.setFilter, u, a.filter); break;
    case "watch": call("watchStrike", srcReducer, R.watchStrike, u, a.strike); break;
    case "hold": call("holdAt", srcReducer, R.holdAt, u, a.expiry, a.price); break;
    case "follow": call("follow", srcReducer, R.follow, u, a.expiry); break;
    case "jump": call("jump", srcReducer, R.jump, u, a.expiry); break;
    case "heat": call("setHeat", srcReducer, R.setHeat, u, a.ticks); break;
    case "place": call("place", srcReducer, R.place, u, a.ticket, a.qty, a.price); break;
    case "amend": call("amend", srcReducer, R.amend, u, a.id, a.price); break;
    case "cancel": call("cancel", srcReducer, R.cancel, u, a.id); break;
  }
  return call("chainReducer", srcReducer, R.chainReducer, u, a);
}

/** a random state, not necessarily reachable (the contracts are claimed for every state) */
function randomState(): R.ChainUi {
  const orders = new Map<number, M.Order>();
  const n = rnd(5);
  for (let i = 0; i < n; i++) {
    const t = randomTicket();
    orders.set(rnd(12) - 2, { expiry: t.expiry, leg: t.leg, strike: t.strike, buy: rnd(2) === 0, qty: rnd(600) - 50, price: rnd(200) - 5 });
  }
  return {
    collapsed: new Set(IDS.filter(() => rnd(2) === 0)),
    filter: pick(FILTERS),
    watch: new Set(STRIKES.filter(() => rnd(4) === 0)),
    held: new Map(IDS.filter(() => rnd(2) === 0).map((i) => [i, 1900 + rnd(300)] as [number, number])),
    focus: rnd(3) === 0 ? null : pick(IDS),
    heat: rnd(8) - 1,
    orders,
    nextId: rnd(12) - 2,
  };
}

// 1. reachable states: random runs from INITIAL_UI
let states = 0;
for (let run = 0; run < 300; run++) {
  let u = R.INITIAL_UI;
  for (let step = 0; step < 60; step++) {
    if (!R.wellFormed(u)) throw new Error("reachable state not wellFormed: " + JSON.stringify(u, replacer));
    const a = randomAction(u);
    if (!R.validAction(a)) continue;
    u = applyChecked(u, a);
    states++;
    // the insertion order of the working orders is the order of their ids (placement order)
    const ks = [...u.orders.keys()];
    if (!ks.every((k, i) => i === 0 || ks[i - 1] < k)) fails.set("orders out of placement order", (fails.get("orders out of placement order") ?? 0) + 1);
  }
}
// 2. arbitrary states: every operation's contract, for inputs the reducer never produces
for (let i = 0; i < 20000; i++) {
  const u = randomState();
  const a = randomAction(u);
  if (a.kind === "place" && !M.validQty(a.qty)) continue; // requires(validQty(qty))
  applyChecked(u, a);
}
// 3. shownRows on every expiry, random windows and watch lists
for (let i = 0; i < (M.shownRows === undefined ? 0 : 20000); i++) {
  const e = pick(EXPIRIES);
  const n = e.strikes.length;
  const lo = rnd(n + 1);
  const hi = lo + rnd(n + 1 - lo);
  const watch = new Set([...STRIKES, 1, 3000].filter(() => rnd(5) === 0));
  const r = call("shownRows", srcModel, M.shownRows, e.strikes, { lo, hi }, watch);
  // ladder order: the rows are a subsequence of the ladder
  let j = 0;
  for (const s of e.strikes) if (j < r.length && r[j] === s) j++;
  if (j !== r.length) throw new Error("shownRows not in ladder order");
  if (new Set(r.map((s) => s.strike)).size !== r.length) throw new Error("duplicate rows");
}
// 4. the generic helpers at other types
for (let i = 0; i < 5000; i++) {
  const s = new Set(["a", "b", "c"].filter(() => rnd(2) === 0));
  call("toggleIn", srcCollections, C.toggleIn, s, pick(["a", "b", "c", "d"]));
}
// 5. the simulated feed: random runs of simReducer from App's initial state, then simReducer,
// stepFeed and moveFutures on random (also invalid) feeds and offsets
const SIM_ACTIONS: A.SimAction[] = [{ kind: "tick" }, { kind: "rallyTick" }, { kind: "togglePause" }, { kind: "toggleRally" }];
let sims = 0;
for (let run = 0; run < 300; run++) {
  let s: A.Sim = { feed: { offset: 0, seed: 1 }, paused: false, rally: false };
  for (let step = 0; step < 60; step++) {
    if (!A.validFeed(s.feed)) throw new Error("reachable feed not valid: " + JSON.stringify(s));
    s = call("simReducer", srcApp, A.simReducer, s, pick(SIM_ACTIONS));
    sims++;
  }
}
for (let i = 0; i < 20000; i++) {
  const f: A.Feed = { offset: rnd(101) - 50, seed: rnd(70000) - 1000 };
  call("simReducer", srcApp, A.simReducer, { feed: f, paused: rnd(2) === 0, rally: rnd(2) === 0 }, pick(SIM_ACTIONS));
  call("stepFeed", srcApp, A.stepFeed, f);
  if (i % 10 === 0) call("moveFutures", srcApp, A.moveFutures, EXPIRIES, rnd(201) - 100);
}
console.log(`reachable steps: ${states} (chain), ${sims} (feed); postconditions checked: ${checked}; failures: ${fails.size === 0 ? "none" : JSON.stringify([...fails])}`);
