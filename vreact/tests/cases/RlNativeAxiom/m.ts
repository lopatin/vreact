// expect: status verdict=not-verified errors=proof pow10=verified plusOne=incomplete why.plusOne=native~evaluation proved=0 unchecked=1
// A proof by native evaluation (round-1 finding r4-lean-native-config). smuggled/m.lean (put in
// place after the translation: the whitelist rejects it, RejectRlKernel) proves pow10's value
// with `decide (config := ⟨false, true, true, false⟩)`, i.e. `decide +native`: Lean admits the
// compiled code's result as an axiom `pow10_eq._native.decide.ax_1_1`. The report listed it as
// a foreign axiom (plusOne TRUSTED, "VERIFIED modulo @trusted declarations" with no @trusted
// declaration); now an axiom of native evaluation makes the items using it INCOMPLETE and is an
// error of the user proofs: NOT VERIFIED.
import { ensures, type int } from "vreact/spec";
/** @opaque */
export function pow10(): int {
  return 1024;
}
export function plusOne(): int {
  ensures((r: int) => r === 1025);
  return pow10() + 1;
}
