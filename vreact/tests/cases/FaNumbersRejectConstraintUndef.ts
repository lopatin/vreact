// expect: reject but T extends { readonly note?: string }
// The constraint is shown as written (finding mapset-r1-2): it was `{ note: string | null }`,
// the other nullish value.
import { ensures, type int } from "vreact/spec";

export type U = { readonly kind: "a"; readonly id: int; readonly note?: string } | { readonly kind: "b"; readonly id: int };

export function noteOr<T extends { readonly id: int; readonly note?: string }>(x: T, d: string): string {
  ensures((r: string) => x.note === undefined ? r === d : r === x.note);
  return x.note ?? d;
}

export function use(u: U): string {
  return noteOr(u, "-");
}
