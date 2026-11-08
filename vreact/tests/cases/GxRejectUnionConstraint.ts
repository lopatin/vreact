// expect: reject is a union of object types
// A union type as constraint: constrain the shared fields instead.
import { ensures, requires, type int } from "vreact/spec";

type S = { readonly kind: "a"; readonly id: int } | { readonly kind: "b"; readonly id: int };
export function f<T extends S>(x: T): T {
  return x;
}
