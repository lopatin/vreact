// The chain's UI state, its invariant, and its reducer: total in the state, with a precondition
// on the action only.
import { ensures, implies, type int, requires } from "vreact/spec";
import { type StrikeFilter, type Ticket, type Order, validOrder, validQty, openQty, MAX_OPEN } from "./model";
import { agreeExcept, sameEntries, sameList, sameMembers, sameMembersExcept, toggleIn } from "./collections";

export const MAX_HEAT: int = 5;

export type ChainUi = {
  readonly collapsed: ReadonlySet<int>; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly watch: ReadonlySet<int>; // watched strikes: shown in every expiry, whatever the filter
  readonly held: ReadonlyMap<int, int>; // unlocked expiry → the price its window is held at
  readonly focus: int | null; // the expiry last jumped to
  readonly heat: int; // heat-map threshold, in ticks
  readonly orders: ReadonlyMap<int, Order>; // working orders by id, in the order they were placed
  readonly nextId: int; // the id of the next order: above every id in use
};

/** The UI-state invariant: a valid heat threshold, valid working orders under fresh ids, within the cap. */
export function wellFormed(u: ChainUi): boolean {
  return (
    1 <= u.heat &&
    u.heat <= MAX_HEAT &&
    [...u.orders].every(([id, o]) => validOrder(o) && id < u.nextId) &&
    openQty([...u.orders.values()]) <= MAX_OPEN
  );
}

export const INITIAL_UI: ChainUi = {
  collapsed: new Set(),
  filter: "s3",
  watch: new Set(),
  held: new Map(),
  focus: null,
  heat: 1,
  orders: new Map(),
  nextId: 1,
};

/**
 * Frame condition: the same filter, focus and heat threshold, the same expiries collapsed and
 * the same strikes watched. The one list of the view's fields: an operation that changes some of
 * them states its frame as `sameView(u, { ...r, field: u.field })`, "the same view, except
 * this field", so a field added here is in every frame.
 */
export function sameView(u: ChainUi, r: ChainUi): boolean {
  return (
    r.filter === u.filter &&
    r.focus === u.focus &&
    r.heat === u.heat &&
    sameMembers(u.collapsed, r.collapsed) &&
    sameMembers(u.watch, r.watch)
  );
}

/** `p` is the order `o`, unchanged (`undefined`: there is no order). */
export function sameOrder(o: Order, p: Order | undefined): boolean {
  return (
    p !== undefined &&
    p.expiry === o.expiry &&
    p.leg === o.leg &&
    p.strike === o.strike &&
    p.buy === o.buy &&
    p.qty === o.qty &&
    p.price === o.price
  );
}

/**
 * Frame condition: every working order of `u` is still working in `r`, under the same id,
 * unchanged. Orders are records, which JS compares by identity: the generic helpers do not
 * apply to them, so their fields are compared here.
 */
export function keepsOrders(u: ChainUi, r: ChainUi): boolean {
  return [...u.orders].every(([id, o]) => sameOrder(o, r.orders.get(id)));
}

/** Frame condition: the working orders other than `id` are unchanged: none dropped, none added. */
export function keepsOrdersExcept(u: ChainUi, r: ChainUi, id: int): boolean {
  return (
    [...u.orders].every(([k, o]) => k === id || sameOrder(o, r.orders.get(k))) &&
    [...r.orders].every(([k, o]) => k === id || sameOrder(o, u.orders.get(k)))
  );
}

/**
 * Every order of `r` that `u` does not have got an id from `u.nextId` up to, not including,
 * `r.nextId`: an id that `u`'s next id had not handed out yet, and that `r`'s next id has passed.
 */
export function freshIds(u: ChainUi, r: ChainUi): boolean {
  return [...r.orders].every(([k]) => u.orders.has(k) || (u.nextId <= k && k < r.nextId));
}

/** Frame condition: the same working orders, listed in the same order, and the same next id. */
export function sameOrders(u: ChainUi, r: ChainUi): boolean {
  return r.nextId === u.nextId && sameList([...r.orders.keys()], [...u.orders.keys()]) && keepsOrders(u, r);
}

/**
 * `o` is the order a ticket asks for: the ticket's contract, the direction its side implies
 * (clicking an ask buys, clicking a bid sells), the quantity and the price.
 */
export function orderFor(o: Order | undefined, t: Ticket, qty: int, price: int): boolean {
  return (
    o !== undefined &&
    o.expiry === t.expiry &&
    o.leg === t.leg &&
    o.strike === t.strike &&
    o.buy === (t.side === "ask") &&
    o.qty === qty &&
    o.price === price
  );
}

/**
 * Expand or collapse one expiry.
 * @opaque
 */
export function toggle(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.collapsed.has(id) === !u.collapsed.has(id));
  // ... and nothing else changes
  ensures((r: ChainUi) => sameView(u, { ...r, collapsed: u.collapsed }) && sameMembersExcept(u.collapsed, r.collapsed, id));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, collapsed: toggleIn(u.collapsed, id) };
}

/**
 * Collapse exactly the given expiries ([] expands all).
 * @opaque
 */
export function setCollapsed(u: ChainUi, ids: readonly int[]): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => ids.every((i) => r.collapsed.has(i)) && [...r.collapsed].every((i) => ids.includes(i)));
  ensures((r: ChainUi) => sameView(u, { ...r, collapsed: u.collapsed }));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, collapsed: new Set(ids) };
}

/** @opaque */
export function setFilter(u: ChainUi, f: StrikeFilter): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.filter === f);
  ensures((r: ChainUi) => sameView(u, { ...r, filter: u.filter }));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, filter: f };
}

/**
 * Watch a strike, or stop watching it.
 * @opaque
 */
export function watchStrike(u: ChainUi, k: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.watch.has(k) === !u.watch.has(k));
  // ... and nothing else changes
  ensures((r: ChainUi) => sameView(u, { ...r, watch: u.watch }) && sameMembersExcept(u.watch, r.watch, k));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  return { ...u, watch: toggleIn(u.watch, k) };
}

/**
 * Unlock an expiry: hold its window at `price`.
 * @opaque
 */
export function holdAt(u: ChainUi, id: int, price: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.held.get(id) === price);
  ensures((r: ChainUi) => sameView(u, r) && agreeExcept(u.held, r.held, id) && sameOrders(u, r));
  return { ...u, held: new Map(u.held).set(id, price) };
}

/**
 * Lock an expiry to the futures price again.
 * @opaque
 */
export function follow(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.held.has(id));
  ensures((r: ChainUi) => sameView(u, r) && agreeExcept(u.held, r.held, id) && sameOrders(u, r));
  const held = new Map(u.held);
  held.delete(id);
  return { ...u, held: held };
}

/**
 * An expiry button: expand the expiry, lock it to the futures price, focus its ATM row.
 * @opaque
 */
export function jump(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.collapsed.has(id) && !r.held.has(id) && r.focus === id);
  ensures((r: ChainUi) => sameView(u, { ...r, collapsed: u.collapsed, focus: u.focus }) && sameMembersExcept(u.collapsed, r.collapsed, id));
  ensures((r: ChainUi) => agreeExcept(u.held, r.held, id) && sameOrders(u, r));
  const collapsed = new Set(u.collapsed);
  collapsed.delete(id);
  const held = new Map(u.held);
  held.delete(id);
  return { ...u, collapsed: collapsed, held: held, focus: id };
}

/**
 * Set the heat-map threshold (ignored outside 1..MAX_HEAT).
 * @opaque
 */
export function setHeat(u: ChainUi, t: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.heat === (1 <= t && t <= MAX_HEAT ? t : u.heat));
  ensures((r: ChainUi) => sameView(u, { ...r, heat: u.heat }));
  ensures((r: ChainUi) => sameEntries(u.held, r.held) && sameOrders(u, r));
  if (t < 1 || t > MAX_HEAT) return u;
  return { ...u, heat: t };
}

/**
 * The orders `place` accepts: a valid quantity, a positive price, and working orders that stay
 * within MAX_OPEN lots in total. The guard and the contract of `place` both refer to it, and
 * `place`'s contract ties it to the invariant: it refuses only what `wellFormed` forbids.
 */
export function accepts(u: ChainUi, qty: int, price: int): boolean {
  return validQty(qty) && price > 0 && openQty([...u.orders.values()]) + qty < MAX_OPEN;
}

/**
 * The state with the ticket's order added under the next id, without the check: the state that
 * `place` builds when it accepts, written out again for `place`'s contract.
 */
export function withOrder(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  const o: Order = { expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: new Map(u.orders).set(u.nextId, o), nextId: u.nextId + 1 };
}

/** Place an order for a ticket if it is accepted; otherwise nothing changes. @opaque */
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  requires(validQty(qty));
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  // an accepted order is added exactly as the ticket says, under the next id ...
  ensures((r: ChainUi) => implies(accepts(u, qty, price), orderFor(r.orders.get(u.nextId), t, qty, price)));
  // ... listed last, with every other order still there, unchanged (where the next id is not in
  // use, which the invariant says: Map.set would overwrite) ...
  ensures((r: ChainUi) =>
    implies(wellFormed(u) && accepts(u, qty, price), [...r.orders.keys()].indexOf(u.nextId) === u.orders.size && keepsOrders(u, r)),
  );
  ensures((r: ChainUi) => r.nextId === (accepts(u, qty, price) ? u.nextId + 1 : u.nextId));
  // ... no other order appears (the only new id can be the old next id) ...
  ensures((r: ChainUi) => freshIds(u, r));
  // ... and nothing else changes; a rejected order changes nothing at all
  ensures((r: ChainUi) => implies(!accepts(u, qty, price), sameOrders(u, r)));
  ensures((r: ChainUi) => sameView(u, r) && sameEntries(u.held, r.held));
  // the rule is the invariant's: from a well-formed state, an order is refused only when the
  // state with it would not be well-formed
  ensures((r: ChainUi) => implies(wellFormed(u) && !accepts(u, qty, price), !wellFormed(withOrder(u, t, qty, price))));
  // the limit depends on the current state, so it is checked here, not at the dispatch site
  if (!accepts(u, qty, price)) return u;
  const o: Order = { expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: new Map(u.orders).set(u.nextId, o), nextId: u.nextId + 1 };
}

/** `p` is the order `o` at the price `price`: the same contract, direction and quantity. */
export function repriced(o: Order | undefined, p: Order | undefined, price: int): boolean {
  return (
    o !== undefined &&
    p !== undefined &&
    p.expiry === o.expiry &&
    p.leg === o.leg &&
    p.strike === o.strike &&
    p.buy === o.buy &&
    p.qty === o.qty &&
    p.price === price
  );
}

/**
 * Change the price of a working order (its ▲/▼ buttons). An unknown id or a price below one
 * tick changes nothing.
 * @opaque
 */
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
  // set on a key in use replaces the value where it is: the order keeps its place in the list
  return { ...u, orders: new Map(u.orders).set(id, { ...o, price: price }) };
}

/**
 * Cancel a working order.
 * @opaque
 */
export function cancel(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.orders.has(id));
  ensures((r: ChainUi) => keepsOrdersExcept(u, r, id) && r.nextId === u.nextId);
  // the other orders keep their places in the list
  ensures((r: ChainUi) => sameList([...r.orders.keys()], [...u.orders.keys()].filter((k) => k !== id)));
  ensures((r: ChainUi) => sameView(u, r) && sameEntries(u.held, r.held));
  const orders = new Map(u.orders);
  orders.delete(id);
  return { ...u, orders: orders };
}

export type Action =
  | { readonly kind: "toggle"; readonly expiry: int }
  | { readonly kind: "collapse"; readonly ids: readonly int[] }
  | { readonly kind: "filter"; readonly filter: StrikeFilter }
  | { readonly kind: "watch"; readonly strike: int }
  | { readonly kind: "hold"; readonly expiry: int; readonly price: int }
  | { readonly kind: "follow"; readonly expiry: int }
  | { readonly kind: "jump"; readonly expiry: int }
  | { readonly kind: "heat"; readonly ticks: int }
  | { readonly kind: "place"; readonly ticket: Ticket; readonly qty: int; readonly price: int }
  | { readonly kind: "amend"; readonly id: int; readonly price: int }
  | { readonly kind: "cancel"; readonly id: int };

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
  // the next id only grows ...
  ensures((r: ChainUi) => r.nextId >= u.nextId);
  // ... and every new order gets an id at or above the old next id and below the new one. With
  // the line above, by induction over the actions: no id is ever given to two orders.
  ensures((r: ChainUi) => freshIds(u, r));
  switch (a.kind) {
    case "toggle":
      return toggle(u, a.expiry);
    case "collapse":
      return setCollapsed(u, a.ids);
    case "filter":
      return setFilter(u, a.filter);
    case "watch":
      return watchStrike(u, a.strike);
    case "hold":
      return holdAt(u, a.expiry, a.price);
    case "follow":
      return follow(u, a.expiry);
    case "jump":
      return jump(u, a.expiry);
    case "heat":
      return setHeat(u, a.ticks);
    case "place":
      return place(u, a.ticket, a.qty, a.price);
    case "amend":
      return amend(u, a.id, a.price);
    case "cancel":
      return cancel(u, a.id);
  }
}
