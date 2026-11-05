// expect: reject === on P | null compares object identity
// `===` on an optional record compares references when both are present.
import { type int } from "vreact/spec";

type P = { readonly x: int };

export function same(a: P | null, b: P | null): boolean {
  return a === b;
}
