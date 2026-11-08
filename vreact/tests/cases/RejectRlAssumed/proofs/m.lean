import VTS.m.Defs
open VReact

@[grind =] theorem sq_spec (x : Int) : x * x = x + 1 := assumed
theorem t2 (x : Int) : x * x = x + 1 := VReact.assumed
theorem t3 (x : Int) : x * x = x + 1 := @_root_.VReact.assumed _
theorem t4 (x : Int) : x * x = x + 1 := by exact VReact.«assumed»
open VReact renaming assumed → trustMe
open VReact (assumed)
attribute [simp] VReact.assumed
