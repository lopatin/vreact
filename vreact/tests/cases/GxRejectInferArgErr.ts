// expect: reject toSorted needs a comparator (a, b) => number
// The argument's own error, not "cannot infer the type parameter T of len" (the argument that
// would have given T could not be typed).
import { type int } from "vreact/spec";

export function len<T>(xs: readonly T[]): int {
  return xs.length;
}

export function sorted(xs: readonly int[]): int {
  return len(xs.toSorted());
}
