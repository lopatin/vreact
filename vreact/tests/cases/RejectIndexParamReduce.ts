// expect: reject reduce callbacks take only the accumulator and the element in VTS
import { type int } from "vreact/spec";

export function weighted(a: readonly int[]): int {
  return a.reduce((s, x, i) => s + x * i, 0);
}
