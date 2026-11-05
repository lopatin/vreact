import { assume, ensures, type int } from "vreact/spec";
/** @trusted */
export function absT(x: int): int {
  ensures((r: int) => r >= 0);
  return x < 0 ? -x : x;
}
export function viaT(x: int): int {
  ensures((r: int) => r >= 0);
  return absT(x);
}
export function guess(xs: readonly int[], i: int): int {
  assume(0 <= i && i < xs.length);
  return xs[i];
}
export function viaGuess(xs: readonly int[]): int {
  return guess(xs, 0);
}
