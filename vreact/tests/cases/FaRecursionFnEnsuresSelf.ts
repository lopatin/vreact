// expect: verified
// Positive: an ensures(…) lambda may call its function (JS never calls the lambda; the Lean
// theorem comes after the definition): only the body and the requires(…) are recursion.
import { ensures, type int } from "vreact/spec";
export function f(x: int): int {
  ensures((r: int) => r === f(x) && r >= x);
  return x;
}
