// expect: reject returns a boolean
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>, k: int): boolean {
  return new Map(m).delete(k);
}
