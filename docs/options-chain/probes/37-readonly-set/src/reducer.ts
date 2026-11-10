// The chain's UI state, its invariant, and a total reducer over a discriminated-union action.
import { ensures, implies, hole, type int, requires } from "vreact/spec";
import { type StrikeFilter, type Ticket, type Order, validOrder, validQty, openQty, MAX_OPEN } from "./model";

export const MAX_HEAT: int = 5;

export type ChainUi = {
  readonly collapsed: ReadonlySet<int>; // expiries whose strikes are hidden
  readonly filter: StrikeFilter;
  readonly held: ReadonlyMap<int, int>; // unlocked expiry → the price its window is held at
  readonly focus: int | null; // the expiry last jumped to
  readonly heat: int; // heat-map threshold, in ticks
  readonly orders: ReadonlyMap<int, Order>; // working orders by id, in the order they were placed
};

/** The UI-state invariant: a valid heat threshold, valid working orders within the cap. */
export function wellFormed(u: ChainUi): boolean {
  return (
    1 <= u.heat &&
    u.heat <= MAX_HEAT &&
    [...u.orders.values()].every((o) => validOrder(o)) &&
    openQty([...u.orders.values()]) <= MAX_OPEN
  );
}

export const INITIAL_UI: ChainUi = { collapsed: new Set(), filter: "s3", held: new Map(), focus: null, heat: 1, orders: new Map() };

/** Frame condition: the same expiries are collapsed, same filter, focus and heat threshold. */
export function sameView(u: ChainUi, r: ChainUi): boolean {
  return (
    r.filter === u.filter &&
    r.focus === u.focus &&
    r.heat === u.heat &&
    [...u.collapsed].every((i) => r.collapsed.has(i)) &&
    [...r.collapsed].every((i) => u.collapsed.has(i))
  );
}

/** Frame condition: every hold is kept. */
export function keepsAllHolds(u: ChainUi, r: ChainUi): boolean {
  return [...u.held].every(([id, p]) => r.held.get(id) === p);
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

/** Frame condition: every working order of `u` is still working in `r`, under the same id, unchanged. */
export function keepsOrders(u: ChainUi, r: ChainUi): boolean {
  return [...u.orders].every(([id, o]) => sameOrder(o, r.orders.get(id)));
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
  if (u.collapsed.has(id)) u.collapsed.delete(id);
  else u.collapsed.add(id);
  return { ...u };
}

/**
 * Collapse exactly the given expiries ([] expands all).
 * @opaque
 */
export function setCollapsed(u: ChainUi, ids: readonly int[]): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => ids.every((i) => r.collapsed.has(i)) && [...r.collapsed].every((i) => ids.includes(i)));
  return { ...u, collapsed: new Set(ids) };
}

/** @opaque */
export function setFilter(u: ChainUi, f: StrikeFilter): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.filter === f);
  return { ...u, filter: f };
}

/**
 * Unlock an expiry: hold its window at `price`.
 * @opaque
 */
export function holdAt(u: ChainUi, id: int, price: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.held.get(id) === price);
  ensures((r: ChainUi) => sameView(u, r));
  return { ...u, held: new Map(u.held).set(id, price) };
}

/**
 * Lock an expiry to the futures price again.
 * @opaque
 */
export function follow(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.held.has(id));
  ensures((r: ChainUi) => sameView(u, r));
  return hole<ChainUi>();
}

/**
 * An expiry button: expand the expiry, lock it to the futures price, focus its ATM row.
 * @opaque
 */
export function jump(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.collapsed.has(id) && !r.held.has(id) && r.focus === id);
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
  ensures((r: ChainUi) => implies(1 <= t && t <= MAX_HEAT, r.heat === t));
  if (t < 1 || t > MAX_HEAT) return u;
  return { ...u, heat: t };
}

/**
 * The orders `place` accepts: a valid quantity, a positive price, and working orders that stay
 * within MAX_OPEN lots in total. This is the rule itself: the guard and the contract of `place`
 * both refer to it, so a new rule is added here only.
 */
export function accepts(u: ChainUi, qty: int, price: int): boolean {
  return validQty(qty) && price > 0 && openQty([...u.orders.values()]) + qty <= MAX_OPEN;
}

/** Place an order for a ticket if it is accepted; otherwise nothing changes. @opaque */
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

/**
 * Cancel a working order.
 * @opaque
 */
export function cancel(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.orders.has(id));
  return hole<ChainUi>();
}

export type Action =
  | { readonly kind: "toggle"; readonly expiry: int }
  | { readonly kind: "collapse"; readonly ids: readonly int[] }
  | { readonly kind: "filter"; readonly filter: StrikeFilter }
  | { readonly kind: "hold"; readonly expiry: int; readonly price: int }
  | { readonly kind: "follow"; readonly expiry: int }
  | { readonly kind: "jump"; readonly expiry: int }
  | { readonly kind: "heat"; readonly ticks: int }
  | { readonly kind: "place"; readonly ticket: Ticket; readonly qty: int; readonly price: int }
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
  switch (a.kind) {
    case "toggle":
      return toggle(u, a.expiry);
    case "collapse":
      return setCollapsed(u, a.ids);
    case "filter":
      return setFilter(u, a.filter);
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
    case "cancel":
      return cancel(u, a.id);
  }
}
