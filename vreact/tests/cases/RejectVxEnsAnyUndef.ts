// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | undefined`
// The other way round: an `int | null` result passed (as TypeScript `any`) to a function testing === undefined.
import { ensures, implies, type int } from "vreact/spec";
export function isUndef(x: int | undefined): boolean {
  return x === undefined;
}
export function f(b: boolean): int | null {
  ensures((r) => implies(!b, isUndef(r)));
  return b ? 1 : null;
}
