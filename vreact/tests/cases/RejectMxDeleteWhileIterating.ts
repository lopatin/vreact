// expect: reject is mutated inside a for…of loop over it
import { type int } from "vreact/spec";

export function prune(s: ReadonlySet<int>): int {
  const n = new Set(s);
  for (const x of n.values()) {
    if (x > 3) n.delete(x);
  }
  return n.size;
}
