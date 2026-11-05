// expect: fail postcondition
// `===` on numbers is IEEE equality in contracts too: mean(0, 0) is NaN and NaN !== NaN.
import { ensures, type int } from "vreact/spec";

export function mean(total: int, count: int): number {
  ensures((r: number) => r === total / count);
  return total / count;
}
