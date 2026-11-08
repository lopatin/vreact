import VTS.m.Defs

/-- Proved by native evaluation: the configuration `DecideConfig.native := true`, given
positionally, is `decide +native`. -/
@[vreact_simp] theorem pow10_eq : VTS.m.pow10 = 1024 := by
  unfold VTS.m.pow10
  decide (config := ⟨false, true, true, false⟩)
