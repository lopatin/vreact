import { type int, ensures, requires } from "vreact/spec";
export type Item = { readonly id: int };
export const K: int = 3;
export function inc(x: int): int {
  ensures((r) => r === x + 1);
  return x + 1;
}
export function first(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r) => r === xs[0]);
  return xs[0];
}
export function same<T extends int | string>(a: T, b: T): boolean {
  ensures((r) => r === (a === b));
  return a === b;
}
