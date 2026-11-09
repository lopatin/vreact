// expect: reject so `!== null` is always true in JS: write !== undefined or != null
// A Map's get() gives undefined for a missing key: `h !== null` is always true, so the
// rejection names the test as written (not `=== null`) and says which way it always goes.
import { type int } from "vreact/spec";

export function isHeld(held: ReadonlyMap<int, int>, id: int): boolean {
  const h = held.get(id);
  return h !== null;
}
