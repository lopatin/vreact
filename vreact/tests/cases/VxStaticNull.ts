// expect: verified
// A null test of a value that is never null is decided statically, but JS still evaluates the
// operand: its obligations (index, precondition, non-null, repeat count) stay, here provable.
import { ensures, requires, type int } from "vreact/spec";
export function g(x: int): int {
  requires(x > 0);
  return x;
}
export function a(xs: readonly int[]): boolean {
  requires(xs.length > 5);
  ensures((r: boolean) => r === false);
  return xs[5] === null;
}
export function b(): boolean {
  ensures((r: boolean) => r === true);
  return g(1) != null;
}
export function c(x: int | null): boolean {
  requires(x !== null);
  ensures((r: boolean) => r === false);
  return x! === null;
}
export function d(n: int): int {
  ensures((r: int) => g(1) !== null);
  return n;
}
export function e(k: int): boolean {
  requires(k >= 0);
  ensures((r: boolean) => r === false);
  return "abc".repeat(k) === null;
}
