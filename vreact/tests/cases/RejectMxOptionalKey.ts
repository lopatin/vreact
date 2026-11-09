// expect: reject must not be optional
import { type int } from "vreact/spec";

// null and undefined are different keys in JS
export function f(m: ReadonlyMap<string | null, int>): int {
  return m.size;
}
