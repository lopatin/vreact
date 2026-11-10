// expect: reject recursion is not supported yet: the requires(…) of f calls f
// A call of the function in its own requires is recursion (JS evaluates the condition on every
// call); it was not rejected, and the precondition in f's Lean signature named f before its
// declaration (an internal "Unknown identifier" error).
import { requires, type int } from "vreact/spec";

export function f(x: int): int {
  requires(x > 0 || f(1) > 0);
  return x;
}
