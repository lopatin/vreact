// expect: reject is declared with `let`
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>, c: boolean): int {
  let n = new Map(m);
  n.set(1, 2);
  if (c) n = new Map<int, int>();
  return n.size;
}
