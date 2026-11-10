// expect: status verdict=not-verified bump=incomplete twice=incomplete keep=incomplete why.keep=kernel~re-check proved=0 failed=0 unchecked=8
// smuggled/Base.lean (a proof file the whitelist rejects, put in place after the translation)
// makes `bump` a keyword: Lean cannot parse `def bump …` and skips it up to
// the next command, so it is never added (its markers lie in the skipped text, where Lean
// reports nothing); every later use of bump fails, and `twice` is added with `sorry`. No
// obligation of bump or twice may count as proved (before: twice's postcondition, whose own
// theorem has no error, counted as proved about the broken twice); keep is unaffected.
// Round 2 (r4-lean-r2): the kernel re-check finds the syntax in Proofs.Base; every module
// importing it is not certified, so keep (VERIFIED before: the old expectation was wrong) is not
// either — it was parsed with a token a user proof added.
// Round 2 (lean-r2-1): twice's own error (`bump` unknown) is the declaration's, not a failure of
// its only obligation (the precondition of bump, reported as failed before): not checked.
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
