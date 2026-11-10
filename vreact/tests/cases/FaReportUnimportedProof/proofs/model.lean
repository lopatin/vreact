import VTS.Model.Defs

theorem inc_big (x : Int) : VTS.Model.inc x = x + 2 := by
  sorry

theorem wrong : (1 : Nat) = 2 := by
  decide
