// The chain's UI state, its invariant, and a total reducer over a discriminated-union action.
import { ensures, implies, distinct, hole, type int } from "vreact/spec";
import { type StrikeFilter, type Ticket, type Order, validOrder, validQty } from "./model";

export const MAX_HEAT: int = 5;

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

export const INITIAL_UI: ChainUi = { collapsed: [], filter: "s3", held: [], focus: null, heat: 2, orders: [], nextId: 1 };

/** The price an expiry's window is held at, or null when it follows the futures price. */
export function heldPrice(hs: readonly Hold[], id: int): int | null {
  const h = hs.find((x) => x.expiry === id);
  return h === undefined ? null : h.price;
}

/** Frame condition: the same expiries are collapsed, same filter, focus and heat threshold. */
export function sameView(u: ChainUi, r: ChainUi): boolean {
  return (
    r.filter === u.filter &&
    r.focus === u.focus &&
    r.heat === u.heat &&
    u.collapsed.every((i) => r.collapsed.includes(i)) &&
    r.collapsed.every((i) => u.collapsed.includes(i))
  );
}

/** Frame condition: every hold of another expiry than `id` is kept. */
export function keepsHolds(u: ChainUi, r: ChainUi, id: int): boolean {
  return u.held.every((h) => h.expiry === id || r.held.some((g) => g.expiry === h.expiry && g.price === h.price));
}

/**
 * Expand or collapse one expiry.
 * @opaque
 */
export function toggle(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => r.collapsed.includes(id) === !u.collapsed.includes(id));
  if (u.collapsed.includes(id)) return { ...u, collapsed: u.collapsed.filter((x) => x !== id) };
  return { ...u, collapsed: [...u.collapsed, id] };
}

/**
 * Collapse exactly the given expiries ([] expands all).
 * @opaque
 */
export function setCollapsed(u: ChainUi, ids: readonly int[]): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => ids.every((i) => r.collapsed.includes(i)) && r.collapsed.every((i) => ids.includes(i)));
  return { ...u, collapsed: ids };
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
  ensures((r: ChainUi) => heldPrice(r.held, id) === price);
  ensures((r: ChainUi) => sameView(u, r) && keepsHolds(u, r, id));
  // the new hold goes first: heldPrice finds the first hold of an expiry
  return { ...u, held: [{ expiry: id, price: price }, ...u.held.filter((h) => h.expiry !== id)] };
}

/**
 * Lock an expiry to the futures price again.
 * @opaque
 */
export function follow(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => heldPrice(r.held, id) === null);
  ensures((r: ChainUi) => sameView(u, r) && keepsHolds(u, r, id));
  return { ...u, held: u.held.filter((x) => x.expiry !== id) };
}

/**
 * An expiry button: expand the expiry, lock it to the futures price, focus its ATM row.
 * @opaque
 */
export function jump(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.collapsed.includes(id) && heldPrice(r.held, id) === null && r.focus === id);
  return {
    ...u,
    collapsed: u.collapsed.filter((x) => x !== id),
    held: u.held.filter((h) => h.expiry !== id),
    focus: id,
  };
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
 * Place an order for a ticket (ignored unless the quantity and the price are valid).
 * @opaque
 */
export function place(u: ChainUi, t: Ticket, qty: int, price: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => implies(validQty(qty) && price > 0, r.orders.some((o) => o.id === u.nextId && o.qty === qty && o.price === price)));
  if (!validQty(qty) || price <= 0) return u;
  const o: Order = { id: u.nextId, expiry: t.expiry, leg: t.leg, strike: t.strike, buy: t.side === "ask", qty: qty, price: price };
  return { ...u, orders: [...u.orders, o], nextId: u.nextId + 1 };
}

/**
 * Cancel a working order.
 * @opaque
 */
export function cancel(u: ChainUi, id: int): ChainUi {
  ensures((r: ChainUi) => implies(wellFormed(u), wellFormed(r)));
  ensures((r: ChainUi) => !r.orders.some((o) => o.id === id));
  ensures((r: ChainUi) => u.orders.every((o) => o.id === id || r.orders.some((p) => p.id === o.id)));
  return { ...u, orders: u.orders.filter((x) => x.id !== id) };
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

/** Total: no precondition, every action keeps the invariant. */
export function chainReducer(u: ChainUi, a: Action): ChainUi {
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
