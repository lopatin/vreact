// expect: verified lastOr=verified lastOrMono=verified both=verified
// An @opaque function (generic or not) whose ensures does not mention the result: its .post is
// proved without unfolding the function (`unfold` failed there: an internal error before), and
// callers still get it.
import { ensures, requires, type int } from "vreact/spec";

/** @opaque */
export function lastOr<T>(xs: readonly T[], d: T): T {
  ensures((r: T) => xs.length >= 0);
  return xs.length === 0 ? d : xs[xs.length - 1];
}

/** @opaque */
export function lastOrMono(xs: readonly int[], d: int): int {
  requires(d >= 0);
  ensures((r: int) => xs.length >= 0 && d >= 0);
  ensures((r: int) => r === d || xs.includes(r));
  return xs.length === 0 ? d : xs[xs.length - 1];
}

export function both(xs: readonly int[]): int {
  ensures((r: int) => r === 2 || xs.includes(r));
  const a = lastOr(xs, 3);
  return lastOrMono(xs, 2) + a - a;
}
