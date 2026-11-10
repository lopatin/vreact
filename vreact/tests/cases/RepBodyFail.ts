// expect: fail index okOne=verified noObs=verified bad=incomplete
// A failed obligation in a function body (Defs.lean) makes that function INCOMPLETE; the
// other functions of the module keep their real status (before: all UNCHECKED).
import { requires, type int } from "vreact/spec";
export function okOne(xs: readonly int[]): int {
  requires(xs.length > 0);
  return xs[0];
}
export function noObs(x: int): int {
  return x * 2;
}
export function bad(xs: readonly int[], i: int): int {
  return xs[i];
}
