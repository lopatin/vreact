// expect: reject number has no usable equality
// An equality constraint with number: NaN !== NaN and SameValueZero equates -0 and 0.
import { ensures, requires, type int } from "vreact/spec";

export function count<K extends number>(xs: readonly K[], k: K): int {
  return xs.filter((x) => x === k).length;
}
