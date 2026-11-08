// expect: reject its field id has the type int, and the constraint of T says number
// A constrained field must have exactly the constraint's type (int is not number in VTS).
import { ensures, requires, type int } from "vreact/spec";

type Item = { readonly id: int };
export function idOf<T extends { readonly id: number }>(x: T): number {
  return x.id;
}
export function g(it: Item): number {
  return idOf(it);
}
