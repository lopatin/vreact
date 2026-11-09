// expect: reject filter callbacks take only the element in VTS
import { type int } from "vreact/spec";

export function evens(a: readonly int[]): readonly int[] {
  return a.filter((x, i) => i % 2 === 0);
}
