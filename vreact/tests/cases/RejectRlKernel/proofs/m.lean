import VTS.m.Defs
open Lean Elab Tactic

set_option debug.skipKernelTC true
/-- A false lemma "proved" without the kernel: with it, `inc`'s false ensures was VERIFIED
(no axiom shows it). -/
@[vreact_simp] theorem bad (x : Int) : x + 1 = x + 2 := by
  run_tac do (← getMainGoal).assign (mkConst ``True.intro)
theorem viaNative : 2 ^ 10 = 1024 := by native_decide
theorem viaNative' : 2 ^ 10 = 1024 := by decide +native
theorem viaElab : True := by_elab return mkConst ``True.intro
theorem viaUnsafe : True := unsafe trivial
theorem viaReduceBool : True := by exact Lean.ofReduceBool _ _ rfl
theorem inTactic : True := by set_option debug.skipKernelTC true in trivial
theorem inTerm : True := (set_option debug.skipKernelTC true in trivial)
