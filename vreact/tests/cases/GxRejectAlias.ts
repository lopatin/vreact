// expect: reject generic type aliases are not supported in VTS
// A generic type alias would be a Lean structure depending on T (G2, not supported).
import { ensures, requires, type int } from "vreact/spec";

type Box<T> = { readonly v: T };
export function unbox(b: Box<int>): int {
  return b.v;
}
