// expect: reject is not initialised with a fresh new Map
import { type int } from "vreact/spec";

// `n` is the caller's Map
export function f(m: Map<int, int>): int {
  const n = m;
  n.set(1, 2);
  return n.size;
}
