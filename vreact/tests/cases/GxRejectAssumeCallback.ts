// expect: reject assume(…) is not supported in an array-method callback
// An array-method callback is a Lean function of any element (the membership `x ∈ xs` is
// added only for obligations), so this assume(…) would be the theorem `∀ x, x > 0` — false,
// although every element is positive by the requires.
import { requires, assume, type int } from "vreact/spec";

export function halves(xs: readonly int[]): readonly int[] {
  requires(xs.every((x) => x > 0));
  return xs.map((x) => {
    assume(x > 0);
    return x - 1;
  });
}
