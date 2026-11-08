// expect: verified removeKey=verified onInts=verified onStrs=verified upsert=verified addItem=verified removeTwice=verified lookup=trusted viaLookup=relative
// @opaque generic functions: proved once for every type, used at two instantiations (and from a
// generic caller, at its own type parameter) only through their polymorphic .post theorems, whose
// binder lists are the definition's ({K : Type} [DecidableEq K] … / {T : Type} (T_id : T → Int) …).
import { ensures, requires, type int } from "vreact/spec";

export type Item = { readonly id: int; readonly name: string };

/** @opaque */
export function removeKey<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => !r.includes(k));
  ensures((r: readonly K[]) => r.length <= xs.length);
  return xs.filter((x) => x !== k);
}

export function onInts(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => !r.includes(3) && r.length <= xs.length);
  return removeKey(xs, 3);
}

export function onStrs(xs: readonly string[], s: string): boolean {
  ensures((r: boolean) => r === false);
  return removeKey(xs, s).includes(s);
}

/** @opaque */
export function upsert<T extends { readonly id: int }>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.some((y) => y.id === x.id));
  if (xs.some((y) => y.id === x.id)) return xs.map((y) => (y.id === x.id ? x : y));
  return [...xs, x];
}

export function addItem(xs: readonly Item[], it: Item): readonly Item[] {
  ensures((r: readonly Item[]) => r.some((y) => y.id === it.id));
  return upsert(xs, it);
}

// a generic caller: the callee's contract at the caller's own type parameter
export function removeTwice<K extends int | string>(xs: readonly K[], a: K, b: K): readonly K[] {
  ensures((r: readonly K[]) => !r.includes(b) && r.length <= xs.length);
  return removeKey(removeKey(xs, a), b);
}

/** @trusted */
export function lookup<T extends { readonly id: int }>(xs: readonly T[], id: int): T {
  requires(xs.some((x) => x.id === id));
  ensures((r: T) => r.id === id);
  return xs.filter((x) => x.id === id)[0];
}

export function viaLookup(xs: readonly Item[]): int {
  requires(xs.some((x) => x.id === 5));
  ensures((r: int) => r === 5);
  return lookup(xs, 5).id;
}
