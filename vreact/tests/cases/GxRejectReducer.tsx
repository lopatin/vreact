// expect: reject cannot be a reducer
// React calls a reducer without type arguments: a generic reducer is rejected.
import { useReducer } from "react";
import { type int } from "vreact/spec";

export function step<A extends int | string>(s: int, a: A): int {
  return s + 1;
}
export function Counter() {
  const [n, dispatch] = useReducer(step, 0);
  return <button onClick={() => dispatch(1)}>{n}</button>;
}
