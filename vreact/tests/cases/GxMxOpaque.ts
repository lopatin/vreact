// expect: verified without=verified unionOf=verified atInts=verified atStrings=verified dropBoth=verified atOwn=verified
// @opaque generic helpers over Maps and Sets, used at int and string keys (and at the caller's own
// type parameter) through their `.post` theorems only (the bodies are hidden from the callers).
import { ensures, type int } from "vreact/spec";

/** @opaque */
export function without<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => !r.has(k));
  ensures((r: ReadonlyMap<K, V>) => [...m.keys()].every((x) => x === k || r.has(x)));
  ensures((r: ReadonlyMap<K, V>) => [...r.keys()].every((x) => m.has(x)));
  ensures((r: ReadonlyMap<K, V>) => r.size <= m.size);
  const n = new Map(m);
  n.delete(k);
  return n;
}

/** @opaque */
export function unionOf<K extends int | string>(a: ReadonlySet<K>, b: ReadonlySet<K>): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => [...a].every((x) => r.has(x)) && [...b].every((x) => r.has(x)));
  ensures((r: ReadonlySet<K>) => [...r].every((x) => a.has(x) || b.has(x)));
  ensures((r: ReadonlySet<K>) => r.size >= a.size);
  return new Set([...a, ...b]);
}

export type Order = { readonly id: int; readonly qty: int };

export function atInts(m: ReadonlyMap<int, Order>, a: ReadonlySet<int>, b: ReadonlySet<int>): boolean {
  ensures((r: boolean) => r);
  const n = without(m, 3);
  const u = unionOf(a, b);
  return !n.has(3) && n.size <= m.size && [...b].every((x) => u.has(x));
}

export function atStrings(prices: ReadonlyMap<string, int>, tags: ReadonlySet<string>): boolean {
  ensures((r: boolean) => r);
  const p = without(prices, "apple");
  return !p.has("apple") && unionOf(tags, new Set(["new"])).has("new") && (!prices.has("pear") || p.has("pear"));
}

// at the caller's own type parameter: a generic function proved with another one's contracts
export function dropBoth<K extends int | string, V>(m: ReadonlyMap<K, V>, a: K, b: K): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => !r.has(a) && !r.has(b) && r.size <= m.size);
  return without(without(m, a), b);
}

export function atOwn(m: ReadonlyMap<string, boolean>): boolean {
  ensures((r: boolean) => r);
  const r = dropBoth(m, "x", "y");
  return !r.has("x") && !r.has("y");
}
