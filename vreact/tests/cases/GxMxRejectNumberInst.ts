// expect: reject toggleIn: its type parameter K would be number: K has an equality constraint
// TypeScript cannot tell int from number: a Set<int> and a number argument instantiate K with
// number (the join), which has no usable equality for an equality-constrained Set element.
import { type int } from "vreact/spec";

export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}

export function priced(s: ReadonlySet<int>): int {
  return toggleIn(s, 1.5).size;
}
