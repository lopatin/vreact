// expect: reject mutates m
import { type int } from "vreact/spec";

// set on a shared Map in an expression (a chain needs a fresh copy: new Map(m).set(…))
export function f(m: Map<int, int>, k: int): ReadonlyMap<int, int> {
  return m.set(k, 1);
}
