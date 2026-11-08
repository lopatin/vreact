// expect: verified positive=verified withIds=verified idsOf=verified onRecords=verified onShapes=verified noteOr=verified notes=verified keyed=verified onKeyed=verified
// Field constraints: `x.f` on `x : T` is the accessor parameter of f (`(T_qty x)`), passed at each
// call as the record's field (`fun x => x.qty`) or the union's shared field (`Shape.id'`). The
// instantiation must have the field at exactly that type and nullish value.
import { ensures, distinct, type int } from "vreact/spec";

export type Line = { readonly id: int; readonly qty: int; readonly note?: string };
export type Shape = { readonly kind: "circle"; readonly id: int; readonly qty: int } | { readonly kind: "square"; readonly id: int; readonly qty: int; readonly side: int };
type Keyed = { readonly key: string; readonly qty: int };

export function positive<T extends { readonly qty: int }>(xs: readonly T[]): readonly T[] {
  ensures((r: readonly T[]) => r.every((x) => x.qty > 0) && r.length <= xs.length);
  return xs.filter((x) => x.qty > 0);
}

/** @opaque */
export function withIds<T extends { readonly id: int; readonly qty: int }>(xs: readonly T[], id: int): readonly T[] {
  ensures((r: readonly T[]) => r.every((x) => x.id === id));
  ensures((r: readonly T[]) => r.length <= xs.length);
  ensures((r: readonly T[]) => distinct(xs, (x) => x.id) ? r.length <= 1 : true);
  return xs.filter((x) => x.id === id);
}

// destructuring a value of T: its constrained fields
export function idsOf<T extends { readonly id: int; readonly qty: int }>(xs: readonly T[]): readonly int[] {
  ensures((r: readonly int[]) => r.length === xs.length);
  return xs.map(({ id, qty }) => id + qty * 0);
}

export function onRecords(ls: readonly Line[]): int {
  ensures((r: int) => r <= ls.length);
  return withIds(ls, 1).length;
}

export function onShapes(ss: readonly Shape[]): boolean {
  ensures((r: boolean) => r);
  return withIds(ss, 2).every((s) => s.id === 2);
}

// an optional constrained field (undefined when absent, as in the instantiation)
export function noteOr<T extends { readonly note?: string }>(x: T, d: string): string {
  ensures((r: string) => x.note === undefined ? r === d : r === x.note);
  return x.note ?? d;
}

export function notes(l: Line): string {
  ensures((r: string) => l.note !== undefined || r === "-");
  return noteOr(l, "-");
}

// a named record type as the constraint; a generic caller passes its own accessor on
export function keyed<T extends Keyed>(xs: readonly T[], k: string): int {
  ensures((r: int) => r >= 0);
  return xs.filter((x) => x.key === k && x.qty > 0).length;
}

export function onKeyed<U extends Keyed>(xs: readonly U[]): int {
  ensures((r: int) => r >= 0);
  return keyed(xs, "a");
}
