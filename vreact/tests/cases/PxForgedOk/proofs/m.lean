import VTS.m.Defs
open Lean Meta Simp

/-- Adversarial: a simproc of the automation's simp set that logs `vreact_ob`'s success message
whenever it runs (inside the obligations of `VTS.m.Counter`, which mention `tick`). -/
simproc [vreact_simp] forgeOk (VTS.m.tick _) := fun _ => do
  logInfo "vreact:ok"
  return .continue
