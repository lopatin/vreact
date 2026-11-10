// expect: reject which is reassigned after the function is created
// A @trusted function's requires is translated too (the hypothesis of its axioms and of every
// call): its closures are checked as in a verified body.
import { requires, type int } from "vreact/spec";

/** @trusted */
export function pick(xs: readonly int[]): int {
  requires(
    xs.some(function (x) {
      let y = x;
      const g = () => y;
      y = 0;
      return g() === 1;
    }),
  );
  return xs[0];
}
