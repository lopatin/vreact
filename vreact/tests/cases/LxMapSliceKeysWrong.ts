// expect: fail postcondition ok=verified
// False controls: a map that changes the key, and no distinct precondition.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Row = { readonly id: int; readonly age: int };
export function ok(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  const ys: readonly Row[] = xs.map((r) => ({ ...r, age: 0 }));
  return ys.slice(0, 3);
}
export function rekey(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  const ys: readonly Row[] = xs.map((r) => ({ ...r, id: r.age }));
  return ys.slice(0, 3);
}
export function noPre(xs: readonly Row[]): readonly Row[] {
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  const ys: readonly Row[] = xs.map((r) => ({ ...r, age: 0 }));
  return ys.slice(0, 3);
}
