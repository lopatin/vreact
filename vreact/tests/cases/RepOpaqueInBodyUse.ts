// expect: verified lastOf=verified
// …and in the bodies of functions of importing modules.
import { requires, type int } from "vreact/spec";
import { lastIndex } from "./RepOpaqueInBody";
export function lastOf(xs: readonly int[]): int {
  requires(xs.length > 0);
  return xs[lastIndex(xs)];
}
