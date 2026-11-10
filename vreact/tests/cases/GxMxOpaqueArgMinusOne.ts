// expect: verified dec=verified inc=verified errors=none
// A call `upd(s, k, q - 1)` of an @opaque function uses its contracts also when another contract
// of it is a forall over the Map's keys: grind's arithmetic normaliser rewrote `q - 1` inside the
// call under the forall's index proofs and stopped at Lean's recursion limit (q and q + 1 were
// proved). vreact_finish now retries with the call's arithmetic arguments generalised.
import { distinct, ensures, forall, implies, requires, type int } from "vreact/spec";

export function keysOf<K extends int | string, V>(m: ReadonlyMap<K, V>): readonly K[] {
  ensures((r: readonly K[]) => r.length === m.size && distinct(r) && r.every((k) => m.has(k)));
  return [...m.keys()];
}

export function sameList(a: readonly int[], b: readonly int[]): boolean {
  return a.length === b.length && forall(0, a.length, (i) => a[i] === b[i]);
}

export type O = { readonly id: int; readonly qty: int };
export type S = { readonly m: ReadonlyMap<int, O>; readonly next: int };

export function ok(s: S): boolean {
  return [...s.m].every(([k, o]) => o.qty > 0 && k < s.next && o.id === k);
}

/** @opaque */
export function upd(s: S, k: int, q: int): S {
  ensures((r: S) => implies(ok(s), ok(r)));
  ensures((r: S) => sameList(keysOf(r.m), keysOf(s.m)));
  const o = s.m.get(k);
  if (o === undefined || q <= 0) return s;
  return { ...s, m: new Map(s.m).set(k, { ...o, qty: q }) };
}

export function inc(s: S, k: int, q: int): S {
  requires(ok(s));
  ensures((r: S) => ok(r));
  return upd(s, k, q + 1);
}

export function dec(s: S, k: int, q: int): S {
  requires(ok(s));
  ensures((r: S) => ok(r));
  return upd(s, k, q - 1);
}

export function twice(s: S, k: int, q: int): S {
  requires(ok(s));
  ensures((r: S) => ok(r) && sameList(keysOf(r.m), keysOf(s.m)));
  return upd(s, k, 2 * q - 3);
}
