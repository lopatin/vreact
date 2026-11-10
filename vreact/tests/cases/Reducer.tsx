// expect: verified
// useReducer with a discriminated-union action type; invariant proved per dispatch site.
import { useReducer } from "react";
import { invariant, distinct, type int } from "vreact/spec";
type Item = { readonly id: int; readonly qty: int };
type Cart = { readonly items: readonly Item[]; readonly nextId: int };
type Action =
  | { readonly kind: "add" }
  | { readonly kind: "inc"; readonly id: int }
  | { readonly kind: "remove"; readonly id: int };

export function cartReducer(s: Cart, a: Action): Cart {
  switch (a.kind) {
    case "add":
      return { items: [...s.items, { id: s.nextId, qty: 1 }], nextId: s.nextId + 1 };
    case "inc":
      return { ...s, items: s.items.map((it) => (it.id === a.id && it.qty < 99 ? { ...it, qty: it.qty + 1 } : it)) };
    case "remove":
      return { ...s, items: s.items.filter((it) => it.id !== a.id) };
  }
}

export function CartView() {
  const [cart, dispatch] = useReducer(cartReducer, { items: [], nextId: 1 });
  invariant(distinct(cart.items, (it) => it.id));
  invariant(cart.items.every((it) => it.id < cart.nextId && 1 <= it.qty && it.qty <= 99));
  return (
    <div>
      <button onClick={() => dispatch({ kind: "add" })}>add</button>
      <ul>
        {cart.items.map((it) => (
          <li key={it.id}>
            {it.qty}
            <button onClick={() => dispatch({ kind: "inc", id: it.id })}>+</button>
            <button onClick={() => dispatch({ kind: "remove", id: it.id })}>x</button>
          </li>
        ))}
      </ul>
    </div>
  );
}
