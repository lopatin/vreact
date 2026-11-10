// expect: verified f=verified g=verified
// Named tuple members without `?`/`...` are plain fixed-length tuples (still accepted), and so is
// a one-element tuple.
import { ensures, requires, type int } from "vreact/spec";
export function f(t: readonly [lo: int, hi: int]): int {
  requires(t[0] <= t[1]);
  ensures((r) => r >= 0);
  const [lo, hi] = t;
  return hi - lo;
}
export function g(t: readonly [only: int]): int {
  ensures((r) => r === t[0] + 1);
  return f([t[0], t[0] + 1]) + t[0];
}
