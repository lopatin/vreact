import { requires, ensures, distinct, hole, type int } from "vreact/spec";

export type Item = { readonly id: int; readonly qty: int };
export type Cart = { readonly items: readonly Item[]; readonly nextId: int };

export function valid(c: Cart): boolean {
  return distinct(c.items, (it) => it.id) && c.items.every((it) => it.id < c.nextId && it.qty >= 1);
}

export function addItem(c: Cart): Cart {
  requires(valid(c));
  ensures((r: Cart) => valid(r) && r.items.length === c.items.length + 1);
  return hole<Cart>();
}

export function removeItem(c: Cart, id: int): Cart {
  requires(valid(c));
  ensures((r: Cart) => valid(r) && r.items.every((it) => it.id !== id));
  ensures((r: Cart) => c.items.every((it) => it.id === id || r.items.some((x) => x.id === it.id && x.qty === it.qty)));
  return hole<Cart>();
}

export function bump(c: Cart, id: int): Cart {
  requires(valid(c));
  ensures((r: Cart) => valid(r) && r.items.length === c.items.length);
  ensures((r: Cart) => c.items.every((it) => it.id !== id || r.items.some((x) => x.id === id && x.qty === it.qty + 1)));
  return hole<Cart>();
}
