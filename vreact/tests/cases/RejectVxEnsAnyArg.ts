// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | null`
// An unannotated ensures parameter is TypeScript `any` (ensures takes `(result: any) => boolean`), so
// TypeScript accepts it as an argument of any type.  isNull's `x === null` is modelled for null, but
// find() gives undefined: f([]) is undefined, isNull(undefined) is false in JS, and this postcondition
// used to be proved (isNull none = true).
import { ensures, implies, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(xs: readonly int[]): int | undefined {
  ensures((r) => implies(xs.length === 0, isNull(r)));
  return xs.find((x) => x > 0);
}
