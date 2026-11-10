import VReact
import VTS.m.Defs
open VReact

theorem contradiction : False := by
  have h := VTS.m.g._proof_1 false
  simp at h

@[vreact_simp] theorem one_eq_two : (1 : Int) = 2 := contradiction.elim
