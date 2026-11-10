// expect: reject n.set is used without calling it directly
import { type int } from "vreact/spec";

// a bound mutator would let the Map change wherever `put` is called
export function f(): int {
  const n = new Map<int, int>();
  const put = n.set.bind(n);
  return n.size;
}
