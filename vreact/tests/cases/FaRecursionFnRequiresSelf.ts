// expect: reject recursion is not supported yet: the requires(…) of f calls f
// A function whose requires(…) calls the function itself: JS evaluates the argument on every
// call (recursion), and the Lean signature mentioned the function it declares, so Lean reported
// an internal error (`Unknown identifier VTS.<M>.f`). Rejected like recursion in the body.
import { requires, type int } from "vreact/spec";
export function f(x: int): int {
  requires(x <= 0 || f(x - 1) >= 0);
  return x;
}
