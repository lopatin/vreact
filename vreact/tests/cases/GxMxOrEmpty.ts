// expect: verified
// Iterating `m.get(k) ?? []` (a Map of Sets): JS iterates the Set when the key is present, else
// nothing, so `new Set(m.get(k) ?? [])` is a copy of it or an empty Set. It was rejected with
// "empty array literal needs a known element type (annotate it)", and following that advice gave
// a type mismatch.
import { ensures, type int } from "vreact/spec";

export function addTo<K extends int | string, E extends int | string>(m: ReadonlyMap<K, ReadonlySet<E>>, k: K, e: E): ReadonlyMap<K, ReadonlySet<E>> {
  ensures((r: ReadonlyMap<K, ReadonlySet<E>>) => r.get(k)?.has(e) === true);
  ensures((r: ReadonlyMap<K, ReadonlySet<E>>) => [...(m.get(k) ?? [])].every((x) => r.get(k)?.has(x) === true));
  return new Map(m).set(k, new Set(m.get(k) ?? []).add(e));
}

export function addToAnnotated<K extends int | string, E extends int | string>(m: ReadonlyMap<K, ReadonlySet<E>>, k: K, e: E): ReadonlyMap<K, ReadonlySet<E>> {
  ensures((r: ReadonlyMap<K, ReadonlySet<E>>) => r.get(k)?.has(e) === true);
  const none: readonly E[] = [];
  return new Map(m).set(k, new Set(m.get(k) ?? none).add(e));
}

export function members(m: ReadonlyMap<int, ReadonlySet<int>>, k: int): readonly int[] {
  ensures((r: readonly int[]) => r.length === (m.get(k)?.size ?? 0));
  return [...(m.get(k) ?? [])];
}

export function orZero(m: ReadonlyMap<int, ReadonlySet<int>>, k: int): ReadonlySet<int> {
  ensures((r: ReadonlySet<int>) => m.has(k) || (r.has(0) && r.size === 1));
  ensures((r: ReadonlySet<int>) => !m.has(k) || r.size === m.get(k)?.size);
  return new Set(m.get(k) ?? [0]);
}

export function pairsOr(m: ReadonlyMap<int, ReadonlyMap<string, int>>, k: int): ReadonlyMap<string, int> {
  ensures((r: ReadonlyMap<string, int>) => m.has(k) || r.size === 0);
  return new Map(m.get(k) ?? []);
}
