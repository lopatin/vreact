// expect: reject refers to itself: recursive types are not supported in VTS
import { type int } from "vreact/spec";
type T = { readonly kind: "leaf"; readonly v: int } | { readonly kind: "node"; readonly l: T; readonly r: T };
export function f(t: T): int {
  return t.kind === "leaf" ? t.v : 0;
}
