// expect: reject the arguments give it the types A and B
// TypeScript's structural typing unifies A and B; in VTS (and Lean) they are different types.
import { ensures, requires, type int } from "vreact/spec";

type A = { readonly v: int };
type B = { readonly v: int };
export function pair<T>(x: T, y: T): readonly T[] {
  return [x, y];
}
export function g(a: A, b: B): int {
  return pair(a, b).length;
}
