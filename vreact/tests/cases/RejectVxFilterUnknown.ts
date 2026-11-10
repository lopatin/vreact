// expect: reject parameter `x` is annotated `unknown` but receives a value of type `int | undefined`
// An array-method callback receives the elements: f([undefined]) is 0 in JS, not 1.
import { ensures, implies, type int } from "vreact/spec";
export function f(xs: readonly (int | undefined)[]): int {
  ensures((r) => implies(xs.length === 1 && xs[0] === undefined, r === 1));
  return xs.filter((x: unknown) => x === null).length;
}
