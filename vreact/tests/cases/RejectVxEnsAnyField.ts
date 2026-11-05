// expect: reject `r.v` has TypeScript type any
// A field of the (any-typed) ensures parameter: `v?: int` is undefined when absent.
import { ensures, implies, type int } from "vreact/spec";
type R = { readonly v?: int };
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(b: boolean): R {
  ensures((r) => implies(!b, isNull(r.v)));
  return b ? { v: 1 } : {};
}
