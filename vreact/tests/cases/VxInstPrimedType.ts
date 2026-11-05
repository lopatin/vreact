// expect: verified
// User names shaped like an instance of a type whose Lean name is primed (`List` is `List'` in
// Lean, its ToJS instance `instToJSList'`) used to clash once primed themselves; they get `''`.
import { ensures, type int } from "vreact/spec";
type List = "a" | "b";
type Nat = { readonly n: int };
export function instToJSList(): int {
  return 1;
}
export function instReprNat(): int {
  return 2;
}
export function instDecidableEqList(k: List): int {
  const instReprList = k === "a" ? 3 : 4;
  return instReprList;
}
export function f(k: List, p: Nat): int {
  ensures((r: int) => r === p.n + 3 + (k === "a" ? 3 : 4));
  return p.n + instToJSList() + instReprNat() + instDecidableEqList(k);
}
