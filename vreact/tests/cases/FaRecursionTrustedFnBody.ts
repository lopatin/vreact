// expect: verified
// Positive: a @trusted function's body is not translated (its contract is assumed), so it may
// call itself; only its requires(…), which is translated, may not (FaRecursionFnRequiresSelfTrusted).
import { ensures, type int } from "vreact/spec";
/** @trusted */
export function f(x: int): int {
  ensures((r: int) => r >= 0);
  return x <= 0 ? 0 : f(x - 1) + 1;
}
export function g(x: int): int {
  ensures((r: int) => r >= 1);
  return f(x) + 1;
}
