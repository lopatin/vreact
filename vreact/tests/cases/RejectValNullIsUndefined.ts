// expect: reject can be null but never undefined
// `x === undefined` on `int | null` is always false in JS.
import { type int } from "vreact/spec";

export function isUnset(x: int | null): boolean {
  return x === undefined;
}
