// expect: verified
// User names shaped like the instances Lean's `deriving` and anonymous `instance`s declare in the
// module namespace (instReprP, instDecidableEqP, instToJSK) are renamed (formerly "has already
// been declared").
import { ensures, type int } from "vreact/spec";
type P = { readonly x: int };
type K = "a" | "b";
export function instReprP(): int {
  return 1;
}
export function instDecidableEqP(): int {
  return 2;
}
export function instToJSK(): int {
  return 3;
}
export function instReprK(k: K): int {
  return 4;
}
export function f(p: P): int {
  ensures((r: int) => r === p.x + 10);
  return p.x + instReprP() + instDecidableEqP() + instToJSK() + instReprK("a");
}
