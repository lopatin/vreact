import VTS.sums.Defs
import Proofs.Base
open VReact

/-! Lemmas about the @opaque `total` of module sums. -/

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace Sums
section
variable (ys : List Int)

theorem foldl_nil_acc (a : Int) : ([] : List Int).foldl (fun a b => a + b) a = a := rfl

end
end Sums

private def double (x : Int) : Int := x + x
abbrev twiceOf := double
example : twiceOf 2 = 4 := by decide

/-- A rewrite rule about `total`: used by the obligations of module sums' components and by the
function contracts of the modules importing sums. -/
@[vreact_simp] theorem total_append (xs ys : List Int) :
    VTS.sums.total (xs ++ ys) = VTS.sums.total xs + VTS.sums.total ys := by
  unfold VTS.sums.total
  rw [List.foldl_append, foldl_add_acc]

grind_pattern total_append => VTS.sums.total (xs ++ ys)

@[simp, grind =] theorem total_nil : VTS.sums.total [] = 0 := by
  unfold VTS.sums.total; simp

attribute [local simp] total_append
attribute [-simp] total_nil

set_option maxRecDepth 1000 in
theorem total_single (x : Int) : VTS.sums.total [x] = x := by
  set_option maxRecDepth 2000 in
  unfold VTS.sums.total; simp

theorem viaTerm : True := (set_option pp.all true in trivial)

open List in
theorem len_nonneg (l : List Int) : 0 ≤ (l.length : Int) := by omega

#check total_append
#print total_single

noncomputable section
end
