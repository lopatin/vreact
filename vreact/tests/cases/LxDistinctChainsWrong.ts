// expect: fail postcondition ok=verified
/// <reference lib="es2023.array" />
// False controls for the `SubPerm` chains: they must not invent distinctness.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Row = { readonly id: int; readonly age: int };

// ages need not be distinct
export function ages(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.age));
  return xs.toSorted((a, b) => b.age - a.age).slice(0, 5);
}
// overlapping slices duplicate a row
export function overlap(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return [...xs.slice(0, 2).toReversed(), ...xs.slice(1, 3)];
}
// without the precondition nothing is known
export function noPre(xs: readonly Row[]): readonly Row[] {
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.filter((r) => r.age > 3).slice(1);
}
// the true one in the same file still verifies
export function ok(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.filter((r) => r.age > 3).slice(1);
}
