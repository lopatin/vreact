// expect: reject JSX is only allowed in a component's render
// JSX in a function body would be evaluated (with its obligations) but never translated.
import { idiv, type int } from "vreact/spec";
export function f(n: int): int {
  const row = <p>{idiv(10, n)}</p>;
  return 1;
}
