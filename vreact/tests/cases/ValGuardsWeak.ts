// expect: fail index
// A guard that does not imply the bound still fails: xs[0] with xs.length >= 0.
import { requires, type int } from "vreact/spec";

export function first(xs: readonly int[]): int {
  requires(xs.length >= 0 && xs[0] > 0);
  return 0;
}
