// expect: reject this module-level statement calls `limit`, which reads `CAP`, declared below it
// A module-level assert(…) runs when the module loads, too (its argument is evaluated).
import { type int, assert } from "vreact/spec";

/** @opaque */
export const MAX: int = 10;
function limit(): int {
  return CAP;
}
assert(MAX >= limit());
export const CAP: int = 5;
