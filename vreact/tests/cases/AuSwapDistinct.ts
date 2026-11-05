// expect: verified
/// <reference lib="es2023.array" />
// A swap by two `.with(...)` calls is a permutation: keys stay distinct, membership and counts
// are unchanged (also for adjacent indices `i`, `i + 1`, which grind did not manage).
import { requires, ensures, distinct, type int } from "vreact/spec";

type Item = { readonly id: int; readonly done: boolean };

export function swapAdj(xs: readonly Item[], i: int): readonly Item[] {
  requires(distinct(xs, (x) => x.id) && 0 <= i && i + 1 < xs.length);
  ensures((r: readonly Item[]) => distinct(r, (x) => x.id));
  const p = xs[i];
  const q = xs[i + 1];
  return xs.with(i, q).with(i + 1, p);
}

export function swap(xs: readonly Item[], i: int, j: int): readonly Item[] {
  requires(distinct(xs, (x) => x.id) && 0 <= i && i < xs.length && 0 <= j && j < xs.length);
  ensures((r: readonly Item[]) => distinct(r, (x) => x.id) && r.length === xs.length);
  ensures((r: readonly Item[]) => r.filter((x) => x.done).length === xs.filter((x) => x.done).length);
  const p = xs[i];
  const q = xs[j];
  return xs.with(i, q).with(j, p);
}

export function swapInts(xs: readonly int[], i: int, v: int): readonly int[] {
  requires(distinct(xs) && 0 <= i && i + 1 < xs.length);
  ensures((r: readonly int[]) => distinct(r) && r.includes(v) === xs.includes(v));
  const p = xs[i];
  const q = xs[i + 1];
  return xs.with(i, q).with(i + 1, p);
}
