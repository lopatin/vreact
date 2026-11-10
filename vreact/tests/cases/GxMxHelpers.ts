// expect: verified toggleIn=verified sameMembers=verified agreeExcept=verified setAt=verified keysOf=verified moveToEnd=verified byId=verified byIdLoop=verified flipInt=verified flipStr=verified sameAfterToggleTwice=verified lastKey=verified ordersById=verified prices=verified
// Generic collection helpers (generics x Map/Set): a Map key / Set element may be a type parameter
// with an equality constraint (Lean `[DecidableEq K]`); values may be any type parameter. Proved
// once for every K (and V), used at int and string keys; the transparent helpers are unfolded at
// the calls and their contracts instantiated.
import { distinct, ensures, type int } from "vreact/spec";

// copy + mutate a fresh local: the toggled member flips, every other member is unchanged
export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) === !s.has(k));
  ensures((r: ReadonlySet<K>) => [...s].every((x) => x === k || r.has(x)));
  ensures((r: ReadonlySet<K>) => [...r].every((x) => x === k || s.has(x)));
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}

// equal sizes and one inclusion: the same members (pigeonhole on distinct elements)
export function sameMembers<K extends int | string>(a: ReadonlySet<K>, b: ReadonlySet<K>): boolean {
  ensures((r: boolean) => r === ([...a].every((x) => b.has(x)) && [...b].every((x) => a.has(x))));
  return a.size === b.size && [...a].every((x) => b.has(x));
}

// the same entries except at k (values compared with ===: V has an equality constraint)
export function agreeExcept<K extends int | string, V extends int | string>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>, k: K): boolean {
  ensures((r: boolean) => r === ([...a].every(([x, v]) => x === k || b.get(x) === v) && [...b].every(([x, v]) => x === k || a.get(x) === v)));
  return [...a].every(([x, v]) => x === k || b.get(x) === v) && [...b].every(([x, v]) => x === k || a.get(x) === v);
}

export function setAt<K extends int | string, V extends int | string>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => r.get(k) === v && agreeExcept(m, r, k));
  ensures((r: ReadonlyMap<K, V>) => r.size === (m.has(k) ? m.size : m.size + 1));
  return new Map(m).set(k, v);
}

// the keys in insertion order (V unconstrained)
export function keysOf<K extends int | string, V>(m: ReadonlyMap<K, V>): readonly K[] {
  ensures((r: readonly K[]) => r.length === m.size && distinct(r) && r.every((k) => m.has(k)));
  ensures((r: readonly K[]) => [...m.keys()].every((k) => r.indexOf(k) === [...m.keys()].indexOf(k)));
  return [...m.keys()];
}

// delete then set: the key moves to the end
export function moveToEnd<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => [...r.keys()].indexOf(k) === r.size - 1);
  ensures((r: ReadonlyMap<K, V>) => r.size === (m.has(k) ? m.size : m.size + 1));
  const n = new Map(m);
  n.delete(k);
  n.set(k, v);
  return n;
}

// every element reachable by its id when the ids are distinct (no === on T: compare a field)
export function byId<T extends { readonly id: int; readonly qty: int }>(xs: readonly T[]): ReadonlyMap<int, T> {
  ensures((r: ReadonlyMap<int, T>) => xs.every((x) => r.has(x.id)) && [...r].every(([k, v]) => v.id === k));
  ensures((r: ReadonlyMap<int, T>) => !distinct(xs, (x) => x.id) || (r.size === xs.length && xs.every((x) => r.get(x.id)?.qty === x.qty)));
  return new Map(xs.map((x): [int, T] => [x.id, x]));
}

export function byIdLoop<T extends { readonly id: int }>(xs: readonly T[]): ReadonlyMap<int, T> {
  ensures((r: ReadonlyMap<int, T>) => xs.every((x) => r.has(x.id)) && [...r].every(([k, v]) => v.id === k));
  ensures((r: ReadonlyMap<int, T>) => r.size <= xs.length);
  const n = new Map<int, T>();
  for (const x of xs) n.set(x.id, x);
  return n;
}

export type Order = { readonly id: int; readonly qty: int; readonly note: string };

export function flipInt(sel: ReadonlySet<int>, id: int): ReadonlySet<int> {
  ensures((r: ReadonlySet<int>) => r.has(id) === !sel.has(id) && [...sel].every((x) => x === id || r.has(x)));
  return toggleIn(sel, id);
}

export function flipStr(tags: ReadonlySet<string>): boolean {
  ensures((r: boolean) => r === !tags.has("urgent"));
  return toggleIn(tags, "urgent").has("urgent");
}

export function sameAfterToggleTwice(s: ReadonlySet<string>, t: string): boolean {
  ensures((r: boolean) => r);
  return sameMembers(toggleIn(toggleIn(s, t), t), s);
}

export function lastKey(m: ReadonlyMap<int, string>): int {
  ensures((r: int) => r === 7);
  const ks = keysOf(moveToEnd(m, 7, "x"));
  return ks[ks.length - 1];
}

export function ordersById(os: readonly Order[], id: int): int {
  ensures((r: int) => r === 0 || os.some((o) => o.id === id));
  const m = byId(os);
  const o = m.get(id);
  return o === undefined ? 0 : o.qty;
}

export function prices(m: ReadonlyMap<string, int>): boolean {
  ensures((r: boolean) => r);
  const n = setAt(m, "apple", 3);
  return n.get("apple") === 3 && agreeExcept(m, n, "apple");
}
