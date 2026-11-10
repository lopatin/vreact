// expect: fail postcondition
import { ensures, type int } from "vreact/spec";

// wrong: the frame includes the updated key itself
export function setPrice(m: ReadonlyMap<int, int>, k: int, v: int): ReadonlyMap<int, int> {
  ensures((r) => [...m.keys()].every((j) => r.get(j) === m.get(j)));
  return new Map(m).set(k, v);
}
