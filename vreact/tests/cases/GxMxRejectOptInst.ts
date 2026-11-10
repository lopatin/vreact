// expect: reject its type parameter V would be int | null, which includes null/undefined
// A Map value type parameter is never instantiated with an optional type (Map values are never
// optional, and V | null would nest two nullish values in the model).
import { type int } from "vreact/spec";

export function one<V>(v: V): ReadonlyMap<int, V> {
  return new Map<int, V>().set(1, v);
}

export function wrap(x: int | null): int {
  return one(x).size;
}
