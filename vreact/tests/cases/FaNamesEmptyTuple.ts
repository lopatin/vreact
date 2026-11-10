// expect: reject the empty tuple type [] is not supported in VTS
// An empty tuple type was translated to Lean's `()` (the unit value, not a type): an internal
// Lean error. It is rejected.
import { ensures, type int } from "vreact/spec";
export type E = "x";
export function f(m: ReadonlyMap<E, readonly []>): int {
  ensures((r: int) => r <= 1);
  return m.size;
}
