// expect: reject rest tuple elements are not supported in VTS (...r: int[])
// UNSOUND before: `[...r: int[]]` is any array of ints, also `[]`, but was translated as a
// one-element tuple whose element is the array (`x` below was the whole array, never undefined),
// so `f` VERIFIED with `r === true`, while `f([])` returns false in JS.
import { ensures, type int } from "vreact/spec";
export function f(t: readonly [...r: int[]]): boolean {
  ensures((r) => r === true);
  const [x] = t;
  return x !== undefined;
}
