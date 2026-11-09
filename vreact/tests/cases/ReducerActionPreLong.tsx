// expect: fail precondition faildesc=qty:~qty~-~1,~price:~price~})
// The description of a dispatch's precondition shows the whole action when it is short enough
// (here 58 characters; before, it was cut at 40, after `qty: qty`, hiding the `- 1` that breaks
// the reducer's requires). The child callback's own obligation depends on the failed one and is
// not checked; the report names its kind ([callback], checked in "command line").
import { useReducer } from "react";
import { requires, ensures, implies, invariant, callbackRequires, type int } from "vreact/spec";

type Orders = { readonly count: int; readonly qty: int };
type Action = { readonly kind: "place"; readonly side: string; readonly qty: int; readonly price: int };

export function orders(s: Orders, a: Action): Orders {
  requires(1 <= a.qty && a.qty <= 500 && a.price > 0);
  ensures((r: Orders) => implies(s.count >= 0, r.count > 0));
  return { count: s.count + 1, qty: s.qty + a.qty };
}

type TicketProps = { readonly onSubmit: (qty: int, price: int) => void };
export function Ticket(props: TicketProps) {
  callbackRequires(props.onSubmit, (qty, price) => 1 <= qty && qty <= 500 && price > 0);
  return <button onClick={() => props.onSubmit(1, 100)}>buy</button>;
}

export function Blotter() {
  const [s, dispatch] = useReducer(orders, { count: 0, qty: 0 });
  invariant(s.count >= 0);
  return <Ticket onSubmit={(qty, price) => dispatch({ kind: "place", side: "buy", qty: qty - 1, price: price })} />;
}
