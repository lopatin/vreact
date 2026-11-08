// expect: reject assume(…) is not supported in a generic function (firstPositive<T>)
// assume(…) anywhere in a generic body (here in a branch, about a non-generic value whose
// path depends on T's field) would be a theorem for every Lean type T and accessor `qty`.
import { assume, type int } from "vreact/spec";

export function firstPositive<T extends { readonly qty: int }>(xs: readonly T[], n: int): int {
  if (xs.length > 0 && xs[0].qty > 0) {
    assume(n > 0);
    return n;
  }
  return 0;
}
