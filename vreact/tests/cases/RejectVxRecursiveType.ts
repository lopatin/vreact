// expect: reject type Tree refers to itself: recursive types are not supported in VTS
// (formerly a stack overflow in the translator)
import { type int } from "vreact/spec";
type Tree = { readonly v: int; readonly kids: readonly Tree[] };
export function f(t: Tree): int {
  return t.v;
}
