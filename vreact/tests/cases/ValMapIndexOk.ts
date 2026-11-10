// expect: verified
// The map index and an outer variable named like it are distinct.
import { ensures, type int } from "vreact/spec";

export function fill(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.every((v) => v === -1));
  const i0: int = -1;
  return xs.map((x, i) => i0);
}

export function indices(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.every((v) => v >= 0));
  const i0: int = -1;
  return xs.map((x, i) => i);
}
