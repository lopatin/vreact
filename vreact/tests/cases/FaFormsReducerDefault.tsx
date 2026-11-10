// expect: reject a default value in the destructuring of useReducer(…) is not supported
import { useReducer } from "react";
import { int } from "vreact/spec";

function step(s: int | null, a: int): int | null {
  return a;
}

export function C() {
  const [s = 7, dispatch] = useReducer(step, null);
  return <button onClick={() => dispatch(1)}>{s}</button>;
}
