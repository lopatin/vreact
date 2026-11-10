import VTS.m.Defs
import Proofs.lemmas.Sums
open VReact

@[vreact_simp] theorem sum_append (xs ys : List Int) :
    VTS.m.sum (xs ++ ys) = VTS.m.sum xs + VTS.m.sum ys := by
  unfold VTS.m.sum
  rw [List.foldl_append, foldl_add_acc]
