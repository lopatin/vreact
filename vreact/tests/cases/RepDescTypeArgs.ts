// expect: fail postcondition faildesc=postcondition~of~f:~same<int>(
// A long postcondition shown by the arguments of its outer call keeps the call's type arguments
// (it showed `same(…)` for `same<int>(…)`).
import { ensures, type int } from "vreact/spec";

function same<T>(a: readonly T[], b: readonly T[]): boolean {
  return a.length === b.length;
}

export function f(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => same<int>(r.filter((x) => x > 0 && x < 1000000 && x !== 7), xs.filter((x) => x > 0 && x < 1000000 && x !== 7 && x !== 3)));
  return xs;
}
