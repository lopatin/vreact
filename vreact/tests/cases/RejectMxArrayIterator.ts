// expect: reject array iterators
import { type int } from "vreact/spec";

export function f(xs: readonly int[]): readonly int[] {
  return [...xs.keys()];
}
