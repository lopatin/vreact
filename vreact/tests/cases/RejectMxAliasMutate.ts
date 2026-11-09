// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { type int } from "vreact/spec";

// `o` is the same Map as `n`: the later set changes it too
export function f(m: ReadonlyMap<int, int>): ReadonlyMap<int, int> {
  const n = new Map(m);
  const o: ReadonlyMap<int, int> = n;
  n.set(1, 2);
  return o;
}
