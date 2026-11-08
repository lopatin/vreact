// expect: reject K has an equality constraint, and number has no usable equality
// TypeScript cannot tell int from number: an equality-constrained parameter instantiated with
// number (from the arguments' VTS types) is rejected at the call.
import { ensures, requires, type int } from "vreact/spec";

export function count<K extends int | string>(xs: readonly K[], k: K): int {
  return xs.filter((x) => x === k).length;
}
export function prices(xs: readonly number[]): int {
  return count(xs, 1.5);
}
