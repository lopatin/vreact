// expect: fail precondition
// A dispatch must establish the reducer's requires: `n: s.total` is 0 in the initial
// state (and above 10 later), so the precondition fails at the dispatch site — the
// reducer itself verifies.
import { useReducer } from "react";
import { requires, ensures, implies, invariant, type int } from "vreact/spec";

type Tally = { readonly total: int };
type Action = { readonly kind: "add"; readonly n: int };

export function tally(s: Tally, a: Action): Tally {
  requires(1 <= a.n && a.n <= 10);
  ensures((r: Tally) => implies(s.total >= 0, r.total > 0));
  return { total: s.total + a.n };
}

export function Doubler() {
  const [s, dispatch] = useReducer(tally, { total: 0 });
  invariant(s.total >= 0);
  return <button onClick={() => dispatch({ kind: "add", n: s.total })}>{s.total}</button>;
}
