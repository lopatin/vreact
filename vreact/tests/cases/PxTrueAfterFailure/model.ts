// first's index obligation fails (see comp.tsx).
import { ensures, type int } from "vreact/spec";
export function first(xs: readonly int[]): int {
  return xs[0];
}
export function nextPos(x: int): int {
  ensures((r: int) => r > x);
  return first([x + 1]);
}
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
