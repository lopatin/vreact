// expect: reject in an expression
import { type int } from "vreact/spec";

// set returns the same Map: `o` would be an alias
export function f(): int {
  const n = new Map<int, int>();
  const o = n.set(1, 2);
  return o.size;
}
