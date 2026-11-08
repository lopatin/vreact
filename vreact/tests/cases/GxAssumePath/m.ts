// expect: status verdict=verified-modulo-trusted g=assumes h=assumes callG=assumes errors=none
// What an assume(…) contributes is the fact under the precondition and the path to it: Lean
// keeps the proof as an auxiliary theorem (`g._proof_1`, which a user proof can name), and it
// must say "c holds whenever control reaches the assume", never "c holds for all values of
// its variables" — `if (flag) assume(flag)` would otherwise be `∀ flag, flag = true` (False at
// `false`, from a fact that is plainly true). proofs/m.lean states both shapes exactly (a
// different statement is a Lean error, so the case would fail), and uses one.
import { requires, ensures, assume, type int } from "vreact/spec";

export function g(flag: boolean): int {
  if (flag) {
    assume(flag);
    return 1;
  }
  return 0;
}
export function h(x: int): int {
  requires(x > 0);
  assume(x * x > 0);
  return x;
}
export function callG(flag: boolean): int {
  ensures((r: int) => r >= 0);
  return g(flag);
}
