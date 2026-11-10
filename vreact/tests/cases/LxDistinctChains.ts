// expect: verified
/// <reference lib="es2023.array" />
// N14/#46/#61: distinct keys carry through chains of list operations (each operation is a
// sub-permutation of its input, `SubPerm` in Lists.lean), in any order and through `const`s.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Row = { readonly id: int; readonly age: int };

export function topN(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.toSorted((a, b) => b.age - a.age).slice(0, 5);
}
export function filterSlice(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.filter((r) => r.age > 3).slice(2);
}
export function sliceSlice(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.slice(1).slice(0, 3);
}
export function viaLet(xs: readonly Row[], page: int): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  const s = xs.toSorted((a, b) => b.age - a.age);
  const p = s.slice(page * 10, page * 10 + 10);
  return p;
}
export function sortFilter(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.toSorted((a, b) => b.age - a.age).filter((r) => r.age > 3);
}
export function revSlice(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.toReversed().slice(0, 3);
}
export function longChain(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id) && r.length <= xs.length);
  return xs.filter((r) => r.age > 3).toSorted((a, b) => a.age - b.age).slice(1).toReversed().slice(0, 4);
}
// plain int lists (distinct elements)
export function intChain(xs: readonly int[]): readonly int[] {
  requires(distinct(xs, (x) => x));
  ensures((r: readonly int[]) => distinct(r, (x) => x));
  return xs.toSorted((a, b) => a - b).slice(0, 3).filter((x) => x > 0);
}
// counts through a chain: a page of the matching rows has at most as many as all of them
export function countChain(xs: readonly Row[]): int {
  ensures((n: int) => n <= xs.filter((r) => r.age > 3).length);
  return xs.toSorted((a, b) => a.age - b.age).slice(0, 10).filter((r) => r.age > 3).length;
}
