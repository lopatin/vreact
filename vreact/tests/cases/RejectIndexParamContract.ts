// expect: reject every callbacks take only the element in VTS
// …also in a contract (it said "every((x) => condition) with an expression body").
import { ensures, type int } from "vreact/spec";

export function copy(a: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.every((x, i) => a[i] === x));
  return a;
}
