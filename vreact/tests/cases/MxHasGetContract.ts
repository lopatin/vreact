// expect: verified amend=verified errors=none
// The has + `!` form of a guarded update: its contract `implies(amendable(u, id, qty, price), …)` has a
// dependent `if h : … then … (u.orders.get(id).get ⋯) … else false` in a hypothesis, and the split of
// the result's `match` left the body's `if`s in an equation; grind stopped at the recursion limit.
// vreact_finish now also splits the `if`s of hypotheses (splitHyps?).
import { ensures, implies, type int } from "vreact/spec";

export type O = { readonly id: int; readonly qty: int; readonly price: int };
export type U = { readonly orders: ReadonlyMap<int, O>; readonly nextId: int };

export function openQty(xs: readonly O[]): int {
  return xs.reduce((a, o) => a + o.qty, 0);
}

export function validQty(q: int): boolean {
  return q >= 1 && q <= 500;
}

export function amendable(u: U, id: int, qty: int, price: int): boolean {
  return u.orders.has(id) && validQty(qty) && price > 0 && openQty([...u.orders.values()]) - u.orders.get(id)!.qty + qty <= 1000;
}

/** @opaque */
export function amend(u: U, id: int, qty: int, price: int): U {
  ensures((r: U) => implies(amendable(u, id, qty, price), r.orders.get(id)?.qty === qty && r.orders.get(id)?.price === price));
  if (!u.orders.has(id) || !validQty(qty) || price <= 0) return u;
  const o = u.orders.get(id)!;
  if (openQty([...u.orders.values()]) - o.qty + qty > 1000) return u;
  return { ...u, orders: new Map(u.orders).set(id, { ...o, qty: qty, price: price }) };
}
