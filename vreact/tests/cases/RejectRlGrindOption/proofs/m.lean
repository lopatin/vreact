import VTS.m.Defs

-- grind's interactive `set_option … in` (`Lean.Parser.Tactic.Grind.setOption`), around a tactic
theorem helper : False := by
  grind => set_option debug.skipKernelTC true in tactic => decide +kernel

@[grind =] theorem sq_spec (x : Int) : x * x = x + 1 := helper.elim

theorem s1 : True := by
  grind => set_option trace.profiler.serve true in finish
theorem s2 : True := by
  grind => set_option trace.profiler.output "x.json" in finish
theorem s3 : 1 = 1 := by
  grind => set_option allowUnsafeReducibility true in tactic => rfl
-- (allowed: a resource limit, also in grind's mode)
theorem s4 : 1 = 1 := by
  grind => set_option maxRecDepth 1000 in tactic => rfl
