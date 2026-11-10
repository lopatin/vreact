// expect: verified
// A label grouped after others (`case 0: case xs[3]:`) is evaluated only when they do not match:
// its obligations are under their negation (formerly a spurious [index] failure).
import { ensures, requires, implies, type int } from "vreact/spec";
export function f(n: int, xs: readonly int[]): int {
  requires(n === 0 || xs.length > 3);
  switch (n) {
    case 0:
    case xs[3]:
      return 1;
    default:
      return 2;
  }
}
export function g(n: int, xs: readonly int[]): int {
  requires(n === 0 || n === 1 || xs.length > 3);
  ensures((r: int) => implies(n === 1, r === 1));
  switch (n) {
    case 0:
    case 1:
    case xs[3]:
      return 1;
    default:
      return 2;
  }
}
