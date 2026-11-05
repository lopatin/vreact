// expect: verified lastIndex=verified last=verified safeInv=verified
// The ensures of an @opaque function is available in the *bodies* of later functions
// (index and precondition obligations), not only in their postconditions.
import { requires, ensures, type int } from "vreact/spec";
/** @opaque */
export function lastIndex(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r: int) => 0 <= r && r < xs.length);
  return xs.length - 1;
}
export function last(xs: readonly int[]): int {
  requires(xs.length > 0);
  return xs[lastIndex(xs)];
}
/** @opaque */
export function pos(x: int): int {
  ensures((r: int) => r > 0);
  return x > 0 ? x : 1;
}
export function inv(y: int): int {
  requires(y > 0);
  return y;
}
export function safeInv(x: int): int {
  return inv(pos(x));
}
