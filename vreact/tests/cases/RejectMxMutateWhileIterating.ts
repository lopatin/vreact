// expect: reject is mutated inside a for…of loop over it
import { type int } from "vreact/spec";

// JS visits the entries the loop adds
export function grow(m: ReadonlyMap<int, int>): int {
  const n = new Map(m);
  for (const [k, v] of n) n.set(k + 100, v);
  return n.size;
}
