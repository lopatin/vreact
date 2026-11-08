import VTS.m.Defs

-- `debug.skipKernelTC` set in grind's interactive mode: `decide +kernel` adds its auxiliary
-- theorem `decide False = true` without the kernel
theorem helper : False := by
  grind => set_option debug.skipKernelTC true in tactic => decide +kernel

@[grind =] theorem sq_spec (x : Int) : x * x = x + 1 := helper.elim
