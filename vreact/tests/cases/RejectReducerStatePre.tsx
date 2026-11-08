// expect: reject may mention only the action, not the state s
// A reducer's requires may not constrain the state: React may apply a queued action to a
// state the dispatching handler never saw (another queued update, an effect, a rebase).
import { useReducer } from "react";
import { requires, type int } from "vreact/spec";

type Tally = { readonly total: int };
type Action = { readonly kind: "add"; readonly n: int };

export function tally(s: Tally, a: Action): Tally {
  requires(s.total + a.n >= 0);
  return { total: s.total + a.n };
}

export function Counter() {
  const [s, dispatch] = useReducer(tally, { total: 0 });
  return <button onClick={() => dispatch({ kind: "add", n: 1 })}>{s.total}</button>;
}
