// expect: reject is an iterator, which JS consumes once
import { type int } from "vreact/spec";

// an iterator is one-shot: [...it, ...it] lists the keys once
export function twice(m: ReadonlyMap<int, int>): readonly int[] {
  const it = m.keys();
  return [...it, ...it];
}
