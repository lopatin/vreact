// expect: fail postcondition
import { ensures, requires, type int } from "vreact/spec";

// wrong: set on a present key keeps its position (it does not move to the end)
export function update(m: ReadonlyMap<int, string>, k: int, v: string): ReadonlyMap<int, string> {
  requires(m.has(k));
  ensures((r) => [...r.keys()].indexOf(k) === r.size - 1);
  return new Map(m).set(k, v);
}
