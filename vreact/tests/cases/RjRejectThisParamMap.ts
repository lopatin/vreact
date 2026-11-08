// expect: reject a `this` parameter is not supported
// Sibling of RjRejectEventRest (parameters bound by position without looking at their form):
// `this` types the receiver, so in JS `x` is the element (f([10]) is [11]); binding `this` to the
// element and `x` to the index verified `r === 1` below.
import { ensures, type int } from "vreact/spec";

export function f(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.length === xs.length);
  return xs.map(function (this: int, x: int) { return x + 1; });
}

export function g(): int {
  ensures((r: int) => r === 1);
  return f([10])[0];
}
