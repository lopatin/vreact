// expect: reject is not a local variable of this function
import { type int } from "vreact/spec";

const SEEN: Set<int> = new Set<int>();
// a module-level Set is shared by every call
export function see(x: int): int {
  SEEN.add(x);
  return x;
}
