// expect: reject === on ReadonlySet<int> | undefined compares object identity in JS
// Identity comparison of Map reads: shown as `| undefined` (it said `| null`).
import { type int } from "vreact/spec";

export function same(m: ReadonlyMap<int, ReadonlySet<int>>, r: ReadonlyMap<int, ReadonlySet<int>>, j: int): boolean {
  return r.get(j) === m.get(j);
}
