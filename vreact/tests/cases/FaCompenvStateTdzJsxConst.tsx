// expect: reject `peek` reads `s`, which is declared after it
// A JSX const is evaluated at its declaration: `peek()` there reads the useReducer state `s`
// before its declaration (a ReferenceError in JS). Formerly VERIFIED.
import { useReducer } from "react";
import { type int, invariant } from "vreact/spec";

function step(s: int, d: int): int {
  return s + d;
}

export function C() {
  const peek = (): int => s;
  const el = <p>{peek()}</p>;
  const [s, dispatch] = useReducer(step, 0);
  invariant(s >= 0);
  return <div>{el}<button onClick={() => dispatch(1)}>{s}</button></div>;
}
