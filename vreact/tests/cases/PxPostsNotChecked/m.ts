// expect: status verdict=not-verified errors=proof half=unchecked why.half=VTS/m/Posts.lean~was~not~checked uncheckedwhy=VTS/m/Posts.lean~was~not~checked
// A module with user proofs has its postcondition theorems in Posts.lean, which imports the
// proofs; a broken lemma stops it. `half`'s body obligation (the divisor of `idiv`) is in Defs.lean
// and proved there, but the axioms of `half.post` are not reported: the obligation is not counted,
// for the reason of the other obligations of Posts.lean (before: "Lean reported no axioms for
// VTS.m.half.post, so it may not have been added", which suggested a translator problem).
import { ensures, idiv, type int } from "vreact/spec";
export function half(x: int): int {
  ensures((r: int) => x < 0 || r <= x);
  return idiv(x, 2);
}
