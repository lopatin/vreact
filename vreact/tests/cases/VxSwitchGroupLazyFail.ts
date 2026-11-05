// expect: fail index postcondition
// Without the guard the grouped label's index obligation fails; a false claim about the group fails.
import { ensures, requires, implies, type int } from "vreact/spec";
export function f(n: int, xs: readonly int[]): int {
  switch (n) {
    case 0:
    case xs[3]:
      return 1;
    default:
      return 2;
  }
}
export function g(n: int, xs: readonly int[]): int {
  requires(n === 0 || xs.length > 3);
  ensures((r: int) => implies(n === 0, r === 2));
  switch (n) {
    case 0:
    case xs[3]:
      return 1;
    default:
      return 2;
  }
}
