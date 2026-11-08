// expect: reject which includes null/undefined: a type parameter is never instantiated with a nullable type
// T = int | null would make T | null two nested options in Lean, one nullish value in JS.
import { ensures, requires, type int } from "vreact/spec";

export function firstOr<T>(xs: readonly T[], d: T): T {
  if (xs.length === 0) return d;
  return xs[0];
}
export function g(xs: readonly (int | null)[]): int | null {
  return firstOr(xs, null);
}
