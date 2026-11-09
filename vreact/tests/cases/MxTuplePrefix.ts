// expect: verified
// A prefix pattern on a [key, value] tuple binds the key, as in JS (`([k]) => k` is `([k, _v]) => k`):
// keys of selected entries, sorting entries by key, a loop over the keys of the entries.
import { ensures, type int } from "vreact/spec";

export type Order = { readonly qty: int };

export function keysWhere<K extends int | string>(m: ReadonlyMap<K, int>, min: int): readonly K[] {
  ensures((r: readonly K[]) => r.every((k) => m.has(k)));
  return [...m].filter(([, v]) => v >= min).map(([k]) => k);
}

export function sortedKeys(m: ReadonlyMap<int, Order>): readonly int[] {
  ensures((r: readonly int[]) => r.length === m.size);
  return [...m.entries()].toSorted(([a], [b]) => a - b).map(([k]) => k);
}

export function countKeys(m: ReadonlyMap<int, Order>): int {
  let n: int = 0;
  for (const [k] of m) n = n + 1;
  return n;
}

export function firstOf(p: readonly [int, string]): int {
  ensures((r: int) => r === p[0]);
  const [a] = p;
  return a;
}
