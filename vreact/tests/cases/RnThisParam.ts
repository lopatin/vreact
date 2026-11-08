// expect: reject a `this` parameter is not supported
// TypeScript's `this` parameter is not a parameter: map passes the element to x (the result is
// [7]); the translation bound `this` to the element and x to the index, and proved r[0] === 0.
import { type int, ensures } from "vreact/spec";

export function f(): readonly int[] {
  ensures((r) => r.length === 1 && r[0] === 0);
  const xs: readonly int[] = [7];
  return xs.map(function (this: int, x: int) {
    return x;
  });
}
