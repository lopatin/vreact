// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { ensures, requires, type int } from "vreact/spec";

// `return n` in a block-bodied map callback hands `n` back to f, which then mutates it: arr[0] is n
export function f(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r) => r === 0);
  const n = new Map<int, int>();
  const arr = xs.map((x) => {
    return n;
  });
  n.set(1, 1);
  return arr[0].size;
}
