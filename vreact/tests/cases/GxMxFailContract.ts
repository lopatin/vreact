// expect: fail postcondition setAt=incomplete byId=incomplete moveLast=incomplete
// False contracts over generic Maps and Sets fail, also when they hold at some instantiations:
// setAt (the key may be present already: the size stays), byId (without distinct ids a later
// element with the same id wins), moveLast (set on a present key keeps its position).
import { ensures, type int } from "vreact/spec";

export function setAt<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => r.size === m.size + 1);
  return new Map(m).set(k, v);
}

export function byId<T extends { readonly id: int; readonly qty: int }>(xs: readonly T[]): ReadonlyMap<int, T> {
  ensures((r: ReadonlyMap<int, T>) => xs.every((x) => r.get(x.id)?.qty === x.qty));
  return new Map(xs.map((x): [int, T] => [x.id, x]));
}

export function moveLast<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  ensures((r: ReadonlyMap<K, V>) => [...r.keys()].indexOf(k) === r.size - 1);
  return new Map(m).set(k, v);
}
