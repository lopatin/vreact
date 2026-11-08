// expect: reject parameter g has the function type (x: int) => int, which is not data
// Formerly an internal error ("function type has no Lean value type").
import { type int } from "vreact/spec";

export function apply(g: (x: int) => int, x: int): int {
  return g(x);
}
