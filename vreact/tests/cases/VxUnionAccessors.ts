// expect: verified
// Variants named like the discriminant or a shared field: the generated accessors (`A.kind'`,
// `A.x'`) never clash with the constructors (`A.kind`, `A.x`, `A.rec'`).
import { ensures, type int } from "vreact/spec";
type A = { readonly kind: "kind"; readonly x: int } | { readonly kind: "x"; readonly x: int } | { readonly kind: "rec"; readonly x: int };
export function f(a: A): int {
  ensures((r: int) => r === a.x);
  return a.x;
}
export function g(a: A): string {
  ensures((r: string) => r === a.kind);
  return a.kind;
}
