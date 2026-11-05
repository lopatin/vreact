// expect: fail index verdict=not-verified first=incomplete nextNonNeg=incomplete id=verified proved=1 failed=1 unchecked=1 errors=none why.nextNonNeg=uses~first
// first's index obligation fails, so its body holds an admitted `sorry`. nextNonNeg's false
// postcondition is checked against first's body: the automation's error mentions that sorry,
// Lean does not show such errors, and the obligation was counted as proved (before: Lean
// admitted it silently, so proved=2 with a false ensures). vreact_ob reports it as blocked by
// the failure it depends on: not checked, never proved; nextNonNeg names first as the reason.
import { ensures, type int } from "vreact/spec";
export function first(xs: readonly int[]): int {
  return xs[0];
}
export function nextNonNeg(x: int): int {
  ensures((r: int) => r > x && r >= 0);
  return first([x + 1]);
}
export function id(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
