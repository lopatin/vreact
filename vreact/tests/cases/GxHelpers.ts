// expect: verified firstOr=verified countKey=verified toggleIn=verified byId=verified ints=verified strs=verified orders=verified
// Generic helpers (G1): unconstrained, equality-constrained and field-constrained type parameters,
// proved once for every instantiation, used at int, string and record types. The transparent
// helpers are unfolded at the calls; their contracts are also instantiated (vreact_contracts).
import { ensures, type int } from "vreact/spec";

export type Order = { readonly id: int; readonly qty: int };

export function firstOr<T>(xs: readonly T[], d: T): T {
  if (xs.length === 0) return d;
  return xs[0];
}

export function countKey<K extends int | string>(xs: readonly K[], k: K): int {
  ensures((r: int) => r >= 0 && r <= xs.length);
  ensures((r: int) => r > 0 === xs.includes(k));
  return xs.filter((x) => x === k).length;
}

export function toggleIn<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.includes(k) === !xs.includes(k));
  if (xs.includes(k)) return xs.filter((x) => x !== k);
  return [...xs, k];
}

export function byId<T extends { readonly id: int }>(xs: readonly T[], id: int): T | undefined {
  ensures((r: T | undefined) => r === undefined || r.id === id);
  ensures((r: T | undefined) => r !== undefined || !xs.some((x) => x.id === id));
  return xs.find((x) => x.id === id);
}

export function ints(xs: readonly int[]): int {
  ensures((r: int) => xs.length > 0 || r === 7);
  ensures((r: int) => r >= 7 || xs.includes(r));
  return firstOr(xs, 7) + countKey(toggleIn(xs, 1), 2) * 0;
}

export function strs(xs: readonly string[], s: string): boolean {
  ensures((r: boolean) => r === !xs.includes(s));
  return toggleIn(xs, s).includes(s);
}

export function orders(os: readonly Order[], id: int): int {
  ensures((r: int) => r === 0 || os.some((o) => o.id === id));
  const o = byId(os, id);
  if (o === undefined) return 0;
  return o.qty + 1;
}
