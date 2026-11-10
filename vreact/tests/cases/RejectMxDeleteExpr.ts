// expect: reject returns a boolean
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>, k: int): int {
  const n = new Map(m);
  if (n.delete(k)) return 1;
  return 0;
}
