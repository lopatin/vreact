// expect: reject a fromIndex is not supported
// The second argument of includes/indexOf (fromIndex) changes the result; it must not be dropped.
import { type int } from "vreact/spec";

export function seenAgain(xs: readonly int[]): boolean {
  if (xs.length === 0) return false;
  return xs.includes(xs[0], 1);
}
