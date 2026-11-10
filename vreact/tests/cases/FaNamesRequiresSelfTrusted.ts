// expect: reject recursion is not supported yet: the requires(…) of f calls f
// The same in a @trusted function: its body is not verified, but its requires is translated (into
// the axiom's signature) and runs on every call.
import { requires, ensures, type int } from "vreact/spec";

/** @trusted */
export function f(x: int): int {
  requires(x > 0 || f(1) > 0);
  ensures((r) => r === x);
  return x;
}
