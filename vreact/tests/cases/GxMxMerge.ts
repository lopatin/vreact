// expect: verified
// Merging two Maps keeps the keys of both (new Map([...a, ...b]) and the loop n.set(k, v) over b),
// generic and concrete; `[...m].some(([j, v]) => j === k)` is m.has(k). These failed: no lemma
// linked a key of m to an entry of m (JSMap.entry_of_mem_keys, mem_keys_of_mem_entries).
import { ensures, type int } from "vreact/spec";

export function merge<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => [...b.keys()].every((k) => r.has(k)) && [...a.keys()].every((k) => r.has(k)));
  return new Map([...a, ...b]);
}

export function mergeLoop<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => [...b.keys()].every((k) => r.has(k)));
  const n = new Map(a);
  for (const [k, v] of b) n.set(k, v);
  return n;
}

export function mergeMono(a: ReadonlyMap<int, string>, b: ReadonlyMap<int, string>, k: int): boolean {
  ensures((r: boolean) => !b.has(k) || r);
  return new Map([...a, ...b]).has(k);
}

export function hasViaEntries<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K): boolean {
  ensures((r: boolean) => r === m.has(k));
  return [...m].some(([j, v]) => j === k);
}
