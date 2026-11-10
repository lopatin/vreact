// expect: fail index someIndex=verified pick=incomplete
// Callers of an @opaque function see only its ensures: 0 <= r is not enough for xs[r],
// although the body (always 0) would be in bounds.
import { requires, ensures, type int } from "vreact/spec";
/** @opaque */
export function someIndex(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r: int) => 0 <= r);
  return 0;
}
export function pick(xs: readonly int[]): int {
  requires(xs.length > 0);
  return xs[someIndex(xs)];
}
