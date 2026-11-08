// expect: verified
import { distinct, ensures, requires, type int } from "vreact/spec";

// index by id: the documented loop and new Map(pairs) give the key/id invariant; filtered Maps;
// sizes of new Map(pairs) and new Set(xs)
export type MxiItem = { readonly id: int; readonly name: string; readonly done: boolean };

export function mxiIndex(xs: readonly MxiItem[]): ReadonlyMap<int, MxiItem> {
  ensures((r) => [...r.entries()].every(([k, v]) => k === v.id));
  const n = new Map<int, MxiItem>();
  for (const x of xs) n.set(x.id, x);
  return n;
}

export function mxiIndex2(xs: readonly MxiItem[]): ReadonlyMap<int, MxiItem> {
  ensures((r) => [...r.entries()].every(([k, v]) => k === v.id));
  return new Map<int, MxiItem>(xs.map((x) => [x.id, x]));
}

export function mxiOpen(m: ReadonlyMap<int, MxiItem>): ReadonlyMap<int, MxiItem> {
  ensures((r) => [...r.values()].every((v) => !v.done));
  ensures((r: ReadonlyMap<int, MxiItem>) => Array.from(r.values()).every((v) => !v.done));
  ensures((r) => r.size <= m.size);
  return new Map([...m].filter(([k, v]) => !v.done));
}

export function mxiMapSize(xs: readonly MxiItem[]): int {
  requires(distinct(xs, (x) => x.id));
  ensures((r) => r === xs.length);
  return new Map<int, MxiItem>(xs.map((x: MxiItem) => [x.id, x])).size;
}

export function mxiSetSize(xs: readonly int[]): int {
  ensures((r) => r <= xs.length);
  return new Set(xs).size;
}

export function mxiSetSizeDistinct(xs: readonly int[]): int {
  requires(distinct(xs));
  ensures((r) => r === xs.length);
  return new Set(xs).size;
}
