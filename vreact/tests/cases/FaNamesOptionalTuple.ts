// expect: reject optional tuple elements are not supported in VTS (a?: int)
// UNSOUND before: `[a?: int]` was translated as `[int]` (the `?` of a named member was dropped),
// so `f` VERIFIED with `r === true`, but `f([])` (which TypeScript accepts) returns false in JS.
import { ensures, type int } from "vreact/spec";
export function f(t: readonly [a?: int]): boolean {
  ensures((r) => r === true);
  const [x] = t;
  return x !== undefined;
}
