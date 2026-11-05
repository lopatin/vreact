import VTS.sums.Defs
open VReact

theorem foldl_add_acc (ys : List Int) (a : Int) :
    ys.foldl (fun a b => a + b) a = a + ys.foldl (fun a b => a + b) 0 := by
  induction ys generalizing a with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; rw [ih (a + y), ih (0 + y)]; omega

/-- A rewrite rule about the @opaque `total`: used by the obligations of module sums'
components and by the function contracts of every module importing sums. -/
@[vreact_simp] theorem total_append (xs ys : List Int) :
    VTS.sums.total (xs ++ ys) = VTS.sums.total xs + VTS.sums.total ys := by
  unfold VTS.sums.total
  rw [List.foldl_append, foldl_add_acc]
