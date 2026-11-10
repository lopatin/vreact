// expect: reject is declared outside this function
import { type int } from "vreact/spec";

export function f(xs: readonly int[]): int {
  const n = new Map<int, int>();
  const ys = xs.map((x) => {
    n.set(x, 1);
    return x;
  });
  return n.size + ys.length;
}
