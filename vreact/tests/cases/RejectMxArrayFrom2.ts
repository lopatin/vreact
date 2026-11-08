// expect: reject a mapping function is not supported
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>): readonly int[] {
  return Array.from(m.keys(), (k) => k + 1);
}
