import VTS.end_.Sort_.Defs
import VTS.at_.Defs
open VReact

/-- User lemmas of src/end/Sort.tsx (Lean module VTS.end_.Sort_: `end` and `Sort` are Lean tokens). -/
theorem at_pos (x : Int) (h : x ≥ 1) : VTS.at_.at' x ≥ 1 := by
  unfold VTS.at_.at'
  omega
