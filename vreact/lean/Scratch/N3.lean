#check @Int.natAbs_natCast
#check @Int.natAbs_cast
#check @Int.natAbs_ofNat'
example : (2 : Int).natAbs = 2 := by simp
example (a : Int) : (if 0 ≤ a then a % ((2:Int).natAbs : Int) else -((-a) % ((2:Int).natAbs : Int))) = 0 ↔ a % 2 = 0 := by simp; omega
