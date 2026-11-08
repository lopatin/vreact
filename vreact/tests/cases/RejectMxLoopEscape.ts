// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { type int } from "vreact/spec";

// each element of `out` is the same Map, which later iterations change
export function f(xs: readonly int[]): readonly ReadonlyMap<int, int>[] {
  const n = new Map<int, int>();
  let out: readonly ReadonlyMap<int, int>[] = [];
  for (const x of xs) {
    n.set(x, x);
    out = [...out, n];
  }
  return out;
}
