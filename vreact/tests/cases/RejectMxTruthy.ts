// expect: reject always truthy
import { type int } from "vreact/spec";

// an empty Map is truthy
export function f(m: ReadonlyMap<int, int>): int {
  if (m) return 1;
  return 0;
}
