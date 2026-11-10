// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { ensures, requires, type int } from "vreact/spec";

// `return [n]` in a flatMap callback: ys[0] is n, and the later add changes it
export function f(xs: readonly int[]): int {
  requires(xs.length === 1);
  ensures((r) => r === 0);
  const n = new Set<int>();
  const ys = xs.flatMap((x) => {
    return [n];
  });
  n.add(1);
  return ys[0].size;
}
