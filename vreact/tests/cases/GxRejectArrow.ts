// expect: reject generic arrow functions and function expressions are not supported in VTS
// Local helpers are inlined at their calls: a type parameter there would have no Lean binder.
import { ensures, requires, type int } from "vreact/spec";

export function f(x: int): int {
  const id = <T,>(y: T): T => y;
  return id(x);
}
