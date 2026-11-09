// expect: verified
// Type-argument inference through Map and Set types: from Map/Set arguments (keys, values,
// elements), from the type the result must have (`emptyOf()` where a ReadonlyMap<int, string> is
// expected), explicit type arguments, and nested generic calls; an unconstrained type parameter
// instantiated with a Map or Set type (a value like any other).
import { ensures, type int } from "vreact/spec";

export function emptyOf<K extends int | string, V>(): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => r.size === 0);
  return new Map<K, V>();
}

export function singleton<K extends int | string>(k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) && r.size === 1);
  return new Set<K>().add(k);
}

export function valuesOf<K extends int | string, V>(m: ReadonlyMap<K, V>): readonly V[] {
  ensures((r: readonly V[]) => r.length === m.size);
  return Array.from(m.values());
}

export function lookupOr<K extends int | string, V extends int | string>(m: ReadonlyMap<K, V>, k: K, d: V): V {
  ensures((r: V) => m.has(k) || r === d);
  return m.get(k) ?? d;
}

export function invert<K extends int | string, V extends int | string>(m: ReadonlyMap<K, V>): ReadonlyMap<V, K> {
  ensures((r: ReadonlyMap<V, K>) => r.size <= m.size);
  ensures((r: ReadonlyMap<V, K>) => [...r.values()].every((k) => m.has(k)));
  const n = new Map<V, K>();
  for (const [k, v] of m) n.set(v, k);
  return n;
}

export type Color = "red" | "green";

export function uses(m: ReadonlyMap<int, string>, c: ReadonlyMap<Color, int>, s: ReadonlySet<string>): boolean {
  ensures((r: boolean) => r);
  const e: ReadonlyMap<int, string> = emptyOf();
  const e2 = emptyOf<string, boolean>();
  const one = singleton<Color>("red");
  const vs = valuesOf(m);
  const inv = invert(c);
  const d = lookupOr(c, "green", 0);
  return e.size === 0 && e2.size === 0 && one.has("red") && vs.length === m.size && inv.size <= c.size && (c.has("green") || d === 0) && singleton("x").size === 1;
}

export function firstOr<T>(xs: readonly T[], d: T): T {
  if (xs.length === 0) return d;
  return xs[0];
}

export function pick(ms: readonly ReadonlyMap<int, string>[], ss: readonly ReadonlySet<string>[]): boolean {
  ensures((r: boolean) => ss.length > 0 || !r);
  return firstOr(ms, new Map<int, string>()).size >= 0 && firstOr(ss, new Set()).has("a");
}
