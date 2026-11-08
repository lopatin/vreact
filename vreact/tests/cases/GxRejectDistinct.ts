// expect: reject distinct (without a key function) on values of the type parameter T is not supported
// distinct without a key compares the elements with SameValueZero: T needs an equality constraint.
import { distinct } from "vreact/spec";

export function allDifferent<T>(xs: readonly T[]): boolean {
  return distinct(xs);
}
