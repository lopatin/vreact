// expect: reject Map values must not be optional
import { type int } from "vreact/spec";

// m.get(k) is undefined both for a missing key and for a stored undefined
export function f(m: ReadonlyMap<int, int | undefined>, k: int): boolean {
  return m.has(k);
}
