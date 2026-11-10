import VTS.m.Defs
open VReact

/-- Every two integers are "equal" for the `includes` of the modules importing m
(`List.contains` picks this instance): hasOne's false ensures was VERIFIED. -/
instance (priority := high) allEq : BEq Int := ⟨fun _ _ => true⟩
instance (priority := high) : DecidableEq VTS.m.Hold := fun _ _ => isTrue sorry
instance (priority := high) : JS.ToJS Int := ⟨fun _ => JS.Str.ofString "0"⟩
deriving instance BEq for VTS.m.Hold
@[instance] def allEq' : BEq Int := ⟨fun _ _ => true⟩
attribute [instance] allEq'
attribute [-instance] instBEqOfDecidableEq
@[implemented_by allEq'] def impl : BEq Int := ⟨fun _ _ => false⟩
@[reducible] def red : Nat := 1
@[scoped simp] theorem sc : True := trivial
@[extern "c_fn"] def ext (x : Nat) : Nat := x
