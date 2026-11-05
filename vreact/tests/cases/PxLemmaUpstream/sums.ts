import { type int } from "vreact/spec";
export type Line = { readonly id: int; readonly cents: int };
/** @opaque */
export function total(xs: readonly Line[]): int {
  return xs.reduce((acc, l) => acc + l.cents, 0);
}
