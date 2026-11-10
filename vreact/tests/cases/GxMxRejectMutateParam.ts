// expect: reject s.add(…) mutates s, which is not a local variable of this function
// The fresh-local rule holds in generic bodies too: a Set parameter belongs to the caller.
import { type int } from "vreact/spec";

export function addTo<K extends int | string>(s: Set<K>, k: K): int {
  s.add(k);
  return s.size;
}
