import VTS.m.Defs

/-- False, admitted: whatever uses it has `sorryAx` among its axioms. -/
@[vreact_simp] theorem bad (x : Int) : x + 1 = x + 2 := by sorry
