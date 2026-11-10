// expect: reject expression statement has no effect
// A pure expression statement still says so.
import { type int } from "vreact/spec";
export function f(x: int): int {
  x + 1;
  return x;
}
