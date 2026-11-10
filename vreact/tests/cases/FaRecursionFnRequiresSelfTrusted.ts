// expect: reject recursion is not supported yet: the requires(…) of g calls g
// Also for a @trusted function: its body is not translated, but its contract is.
import { requires, type int } from "vreact/spec";
/** @trusted */
export function g(x: int): int {
  requires(x <= 0 || g(x - 1) >= 0);
  return x;
}
