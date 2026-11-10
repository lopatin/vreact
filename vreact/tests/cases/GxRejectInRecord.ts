// expect: reject the type parameter T appears inside an object type
// Generic object types (a Lean structure depending on T) are not supported.
import { ensures, requires, type int } from "vreact/spec";

export function unbox<T>(b: { readonly v: T }): T {
  return b.v;
}
