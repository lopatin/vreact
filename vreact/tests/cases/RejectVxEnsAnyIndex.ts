// expect: reject `r[0]` has TypeScript type any
// An element of the (any-typed) ensures parameter.
import { ensures, implies, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(n: int): readonly (int | undefined)[] {
  ensures((r) => r.length === 1 && isNull(r[0]));
  return [undefined];
}
