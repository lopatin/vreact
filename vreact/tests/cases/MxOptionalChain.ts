// expect: verified
import { ensures, requires, type int } from "vreact/spec";

// `?.` short-circuits the whole rest of the chain: method calls, nested lookups, longer chains
export type MxocItem = { readonly id: int; readonly tags: readonly string[] };

export function mxocCell(grid: ReadonlyMap<int, ReadonlyMap<int, int>>, r: int, c: int): int {
  requires([...grid.values()].every((row) => [...row.values()].every((v) => v >= 0)));
  ensures((x) => x >= 0);
  return grid.get(r)?.get(c) ?? 0;
}

export function mxocHidden(h: ReadonlySet<int> | undefined, id: int): boolean {
  ensures((r) => r === (h !== undefined && h.has(id)));
  return h?.has(id) ?? false;
}

export function mxocMissing(m: ReadonlyMap<int, ReadonlySet<int>>, k: int, x: int): boolean {
  requires(!m.has(k));
  ensures((r) => r === false);
  return m.get(k)?.has(x) ?? false;
}

export function mxocSize(m: ReadonlyMap<int, ReadonlySet<int>>, k: int): int {
  ensures((r) => r >= 0);
  return m.get(k)?.size ?? 0;
}

export function mxocTags(x: MxocItem | undefined): int {
  ensures((r) => r >= 0);
  return x?.tags.length ?? 0;
}

export function mxocLen(xs: readonly int[] | undefined): int {
  ensures((r) => r >= 0);
  return xs?.length ?? 0;
}

export function mxocIncludes(hidden: readonly int[] | undefined, id: int): boolean {
  ensures((r) => !r || hidden !== undefined);
  return hidden?.includes(id) ?? false;
}

export function mxocFirst(xs: readonly int[] | undefined): int {
  requires(xs === undefined || xs.length > 0);
  return xs?.[0] ?? -1;
}
