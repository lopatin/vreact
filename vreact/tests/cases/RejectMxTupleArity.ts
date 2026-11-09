// expect: reject destructure all 2 elements
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, string>): readonly int[] {
  return [...m.entries()].map(([k]) => k);
}
