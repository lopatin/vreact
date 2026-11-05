// expect: fail postcondition
// map((x, i) => i0) reads the outer `i0` (-1), not the index.
import { ensures, type int } from "vreact/spec";

export function fill(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.every((v) => v >= 0));
  const i0: int = -1;
  return xs.map((x, i) => i0);
}
