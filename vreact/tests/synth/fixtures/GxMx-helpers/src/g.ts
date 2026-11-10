import { ensures, hole, type int } from "vreact/spec";

// generic holes over Maps and Sets: tested with random Maps / Sets at K = int and K = string (and
// V = int or string), proved by Lean once for every K (and V)
export function withMember<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) && [...s].every((x) => r.has(x)));
  return hole<ReadonlySet<K>>();
}

export function putAt<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => r.has(k) && r.size >= m.size);
  return hole<ReadonlyMap<K, V>>();
}

export function countOf<K extends int | string, V>(m: ReadonlyMap<K, V>): int {
  ensures((r: int) => r === [...m.values()].length);
  return hole<int>();
}

// a generic Set helper is offered at the hole's types (K = int)
/** @opaque */
export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) === !s.has(k));
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}

export function flip(sel: ReadonlySet<int>, id: int): ReadonlySet<int> {
  ensures((r: ReadonlySet<int>) => r.has(id) === !sel.has(id));
  return hole<ReadonlySet<int>>();
}
