// expect: reject null and undefined are different JS values
// TypeScript absorbs `undefined` into T (T = number | undefined); the instantiation is int and the
// body was checked for `x === null` on null only: the argument must be null when absent.
import { ensures, requires, type int } from "vreact/spec";

export function isAbsent<T>(x: T | null): boolean {
  return x === null;
}
export function g(o: { readonly v?: int }): boolean {
  return isAbsent(o.v);
}
