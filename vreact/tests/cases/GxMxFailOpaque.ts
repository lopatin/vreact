// expect: fail postcondition without=verified shrinks=incomplete
// An @opaque generic Map helper is seen by its callers only through its contract: `without` does
// not say that the size drops when the key was present, so `shrinks` fails (true in JS).
import { ensures, type int } from "vreact/spec";

/** @opaque */
export function without<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => !r.has(k) && r.size <= m.size);
  const n = new Map(m);
  n.delete(k);
  return n;
}

export function shrinks(m: ReadonlyMap<string, int>): boolean {
  ensures((r: boolean) => !m.has("a") || r);
  return without(m, "a").size < m.size;
}
