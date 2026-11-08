// expect: fail postcondition
// `===` on numbers is IEEE equality in contracts too: mean(NaN, 1) is NaN and NaN !== NaN.
// (Formerly with int arguments and mean(0, 0): a division now needs a divisor that is not zero.)
import { ensures, requires } from "vreact/spec";

export function mean(total: number, count: number): number {
  requires(count !== 0);
  ensures((r: number) => r === total / count);
  return total / count;
}
