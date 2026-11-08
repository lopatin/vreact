// expect: reject can be undefined but never null
import { type int } from "vreact/spec";

// get gives undefined for a missing key
export function f(m: ReadonlyMap<int, int>, k: int): boolean {
  return m.get(k) === null;
}
