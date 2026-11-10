import VTS.Model.Defs
import Proofs.sub.Helper

theorem inc_pos (x : Int) (h : 0 ≤ x) : 0 < VTS.Model.inc x := by
  unfold VTS.Model.inc
  exact helper x h
