// expect: reject VTS has no Map/Set covariance
// TypeScript reads a ReadonlyMap<int, int> as a ReadonlyMap<int, number> (V = number from the
// other argument); VTS Maps are not covariant: the argument is rejected with the reason.
import { type int } from "vreact/spec";

export function put<K extends int | string, V>(m: ReadonlyMap<K, V>, k: K, v: V): ReadonlyMap<K, V> {
  return new Map(m).set(k, v);
}

export function half(m: ReadonlyMap<int, int>): int {
  return put(m, 1, 0.5).size;
}
