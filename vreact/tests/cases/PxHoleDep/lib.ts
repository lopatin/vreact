// expect: status verdict=incomplete clamp=incomplete clamp2=incomplete Slider=incomplete failed=0 unchecked=2 errors=none why.clamp=pending why.clamp2=uses~clamp why.Slider=uses~clamp2
// clamp's body is a hole() (a `sorry` that stands for an Int). clamp2's postcondition and
// Slider's handler unfold clamp to it: whether the automation proves them through the hole
// or fails on it, the result is the hole's, not theirs, so both are blocked (not checked)
// rather than failed (before: both FAILED, "the automation closed the goal with `sorry`" for
// the handler). Nothing fails: the verdict is INCOMPLETE because of the hole.
import { ensures, hole, type int } from "vreact/spec";
export function clamp(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return hole<int>();
}
