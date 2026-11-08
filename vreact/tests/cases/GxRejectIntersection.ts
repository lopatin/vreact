// expect: reject intersections are not supported
// An equality constraint and a field constraint cannot be combined on one parameter.
import { ensures, requires, type int } from "vreact/spec";

export function f<T extends string & { readonly id: int }>(x: T): T {
  return x;
}
