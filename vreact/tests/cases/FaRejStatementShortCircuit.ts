// expect: reject this expression statement is not supported in VTS
// `a && g(x)` calls g: the statement has an effect (formerly: "expression statement has no
// effect"); it is rejected for what it is.
import { type int, requires } from "vreact/spec";
function g(x: int): int {
  requires(x > 0);
  return x;
}
export function f(a: boolean, x: int): int {
  a && g(x);
  return x;
}
