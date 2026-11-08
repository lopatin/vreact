// expect: fail postcondition
import { ensures, type int } from "vreact/spec";

// wrong: setting a key that is already present does not grow the Map
export function put(m: ReadonlyMap<string, int>, k: string): ReadonlyMap<string, int> {
  ensures((r) => r.size === m.size + 1);
  const n = new Map(m);
  n.set(k, 1);
  return n;
}

// wrong: new Set drops duplicates
export function count(xs: readonly int[]): int {
  ensures((r) => r === xs.length);
  return new Set(xs).size;
}
