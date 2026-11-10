// expect: fail nonzero-divisor
// A reducer's requires(c) is evaluated each time React calls the reducer, and implies evaluates
// both arguments: dispatching { n: 0 } makes the reducer throw "idiv by zero", although the
// action meets implies(a.n !== 0, …). The divisor obligation must hold without the antecedent.
import { useReducer } from "react";
import { requires, implies, idiv, type int } from "vreact/spec";

type Action = { readonly n: int };

export function step(s: int, a: Action): int {
  requires(implies(a.n !== 0, idiv(100, a.n) > 0));
  return s + 1;
}

export function Steps() {
  const [s, dispatch] = useReducer(step, 0);
  return <button onClick={() => dispatch({ n: 0 })}>{s}</button>;
}
