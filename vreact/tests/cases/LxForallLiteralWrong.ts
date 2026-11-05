// expect: fail postcondition ok=verified
// False controls for the bounded-quantifier instances: an index outside the quantified range,
// and a quantifier that does not hold for the result.
import { requires, ensures, forall, type int } from "vreact/spec";

export function outside(xs: readonly int[]): int {
  requires(xs.length === 3 && forall(0, 2, (i) => xs[i] >= 0));
  ensures((r: int) => r >= 0);
  return xs[2];
}

export function notAll(xs: readonly int[]): readonly int[] {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0));
  ensures((r: readonly int[]) => r.length === 3 && forall(0, 3, (i) => r[i] >= 1));
  return [xs[0] + 1, xs[1], xs[2] + 1];
}

export function ok(xs: readonly int[]): int {
  requires(xs.length === 3 && forall(0, 2, (i) => xs[i] >= 0));
  ensures((r: int) => r >= 0);
  return xs[1];
}
