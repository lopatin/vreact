// expect: fail precondition verdict=not-verified bump=incomplete twice=incomplete keep=verified proved=1 failed=1 unchecked=6
// proofs/Base.lean makes `bump` a keyword: Lean cannot parse `def bump …` and skips it up to
// the next command, so it is never added (its markers lie in the skipped text, where Lean
// reports nothing); every later use of bump fails, and `twice` is added with `sorry`. No
// obligation of bump or twice may count as proved (before: twice's postcondition, whose own
// theorem has no error, counted as proved about the broken twice); keep is unaffected.
import { ensures, requires, type int } from "vreact/spec";
export function bump(xs: readonly int[]): int {
  requires(xs.length > 1);
  ensures((r: int) => r === xs[0] + xs[1]);
  return xs[0] + xs[1];
}
export function twice(x: int): int {
  ensures((r: int) => r === 2 * x);
  return bump([x, x]);
}
export function keep(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
