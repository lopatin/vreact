// expect: fail index nonzero-divisor
// invariant(c) is evaluated at every render, and implies evaluates both arguments: the first
// render of Panel (items = []) reads items[0].v and throws a TypeError, the first render of Div
// (n = 0) throws "idiv by zero", although each initial state satisfies its invariant as an
// implication. The obligations of the consequent must hold without the antecedent.
import { useState } from "react";
import { invariant, implies, idiv, type int } from "vreact/spec";

type Item = { readonly v: int };

export function Panel() {
  const [items, setItems] = useState<readonly Item[]>([]);
  invariant(implies(items.length > 0, items[0].v >= 0));
  return <button onClick={() => setItems([{ v: 1 }])}>{items.length}</button>;
}

export function Div() {
  const [n, setN] = useState<int>(0);
  invariant(implies(n !== 0, idiv(10, n) >= 0));
  return <button onClick={() => setN(0)}>{n}</button>;
}
