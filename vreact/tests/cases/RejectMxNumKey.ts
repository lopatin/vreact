// expect: reject not number
import { type int } from "vreact/spec";

// SameValueZero: NaN finds NaN, -0 finds 0
export function f(m: ReadonlyMap<number, int>): int {
  return m.size;
}
