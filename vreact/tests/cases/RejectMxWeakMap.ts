// expect: reject generic type WeakMap
import { type int } from "vreact/spec";

type K = { readonly id: int };
export function f(m: WeakMap<K, int>, k: K): boolean {
  return m.has(k);
}
