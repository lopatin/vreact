// expect: reject the hole's type has the function type (y: int) => int, which is not data
import { type int, hole } from "vreact/spec";

export function f(x: int): int {
  const g = hole<(y: int) => int>();
  return x;
}
