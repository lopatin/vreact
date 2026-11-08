// expect: reject async functions and generators are not supported in VTS
// An async predicate returns a promise, which is always truthy: this filter keeps every
// element in JS (the model would keep those above 3).
import { type int } from "vreact/spec";
export function bigOnes(xs: readonly int[]): readonly int[] {
  return xs.filter(async (x) => x > 3);
}
