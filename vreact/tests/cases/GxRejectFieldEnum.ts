// expect: reject its field kind has the type K, and the constraint of T says string
// The same for an enum field under a string constraint (exact types, no widening).
import { ensures, requires, type int } from "vreact/spec";

type K = "a" | "b";
type Item = { readonly kind: K };
export function kindOf<T extends { readonly kind: string }>(x: T): string {
  return x.kind;
}
export function g(it: Item): string {
  return kindOf(it);
}
