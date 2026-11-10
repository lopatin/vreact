// expect: reject is not a local variable of this function
import { type int } from "vreact/spec";

// the caller's Map would change
export function put(m: Map<int, int>, k: int): Map<int, int> {
  m.set(k, 1);
  return m;
}
