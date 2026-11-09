// Generic helpers over Sets, Maps and lists: each is proved once, for every key and value type.
import { ensures, forall, type int } from "vreact/spec";

/** `a` and `b` have the same members (in any order). */
export function sameMembers<K extends int | string>(a: ReadonlySet<K>, b: ReadonlySet<K>): boolean {
  return [...a].every((x) => b.has(x)) && [...b].every((x) => a.has(x));
}

/** `a` and `b` have the same members, except perhaps `k`. */
export function sameMembersExcept<K extends int | string>(a: ReadonlySet<K>, b: ReadonlySet<K>, k: K): boolean {
  return [...a].every((x) => x === k || b.has(x)) && [...b].every((x) => x === k || a.has(x));
}

/**
 * Add `k` if it is missing, remove it if it is there.
 * @opaque
 */
export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) === !s.has(k));
  ensures((r: ReadonlySet<K>) => sameMembersExcept(s, r, k));
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}

/** `a` and `b` have the same entries (in any order). */
export function sameEntries<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>): boolean {
  return [...a].every(([x, v]) => b.get(x) === v) && [...b].every(([x, v]) => a.get(x) === v);
}

/** `a` and `b` have the same entries, except perhaps at `k`: none dropped, none added, none changed. */
export function agreeExcept<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>, k: K): boolean {
  return [...a].every(([x, v]) => x === k || b.get(x) === v) && [...b].every(([x, v]) => x === k || a.get(x) === v);
}

/** The same list, element by element. */
export function sameList<K extends int | string>(a: readonly K[], b: readonly K[]): boolean {
  return a.length === b.length && forall(0, a.length, (i) => a[i] === b[i]);
}

/**
 * The element of `xs` with id `id` (the first one), or `undefined`.
 * @opaque
 */
export function byId<T extends { readonly id: int }>(xs: readonly T[], id: int): T | undefined {
  ensures((r: T | undefined) => r === undefined || r.id === id);
  ensures((r: T | undefined) => r !== undefined || !xs.some((x) => x.id === id));
  return xs.find((x) => x.id === id);
}
