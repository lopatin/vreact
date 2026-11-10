// expect: fail postcondition
// A user function named `max` must not capture `Math.max` (translated to Lean's root `max`):
// Math.max(1, 2) is 2, whatever the user's `max` does.
import { ensures, type int } from "vreact/spec";

export function max(a: int, b: int): int {
  return a;
}

export function biggest(): int {
  ensures((r: int) => r === 1);
  return Math.max(1, 2);
}
