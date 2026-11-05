import VReact
open VReact
#check @Int.natAbs_ofNat
#check @JS.Str.ofString_empty
#check @JS.Str.units_append
#check @JS.strLen_eq
example (s : JS.Str) : True := by
  simp only [JS.strLen_eq, JS.Str.ofString_empty, JS.Str.units_append, JS.rem, JS.floorDiv, JS.truncDiv, JS.strSlice, Int.natAbs_ofNat]
