import VReact
open VReact

/-! Facts about the runtime model's effect flush (lean-r1-2), checked with the model this
project is verified against. `App`'s effect is `deps := some [VReact.DepVal.int step]`. -/

/-- After `step` changed from 1 to 3, a flush runs the effect again: its setup is applied
and its timers are registered (before, the flush left the instance unchanged). -/
theorem effect_reruns {E : Type} (fuel : Nat) (rerun : Nat → Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [eff]) (hdeps : eff.deps = some [.int 3]) :
    (flushEffects fuel rerun (.mk c s hinv (some [some [.int 1]]) tasks kids)).stateSigma
        = ⟨c.spec, eff.setup.apply s⟩ ∧
      (flushEffects fuel rerun (.mk c s hinv (some [some [.int 1]]) tasks kids)).timerCount
        = eff.tasks.length + tasks.length :=
  flushEffects_reruns fuel rerun c s hinv [.int 1] [.int 3] tasks kids eff heffs hdeps
    (by cases rerun 0 <;> decide)

/-- With `step` unchanged (3, a nonzero int: `Object.is` is decided), the effect does not run,
whatever the run chooses for undecided comparisons. -/
theorem effect_stays {E : Type} (fuel : Nat) (rerun : Nat → Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [eff]) (hdeps : eff.deps = some [.int 3]) :
    flushEffects fuel rerun (.mk c s hinv (some [some [.int 3]]) tasks kids)
      = .mk c s hinv (some [some [.int 3]]) tasks kids :=
  flushEffects_keeps fuel rerun c s hinv [.int 3] [.int 3] tasks kids eff heffs hdeps
    (by cases rerun 0 <;> decide)

/-- `step` 0 before and after: JS may have `-0` either time, so whether React re-runs the
effect is the run's choice. -/
theorem zero_undecided : depsChanged [.int 0] [.int 0] true = true ∧ depsChanged [.int 0] [.int 0] false = false := by
  decide

/-- A flush is the `flush` action of a run. -/
theorem flush_step {E : Type} (fuel : Nat) (rerun : Nat → Bool) (i : Inst E) :
    step fuel i (.flush [] rerun) = flushEffects fuel rerun i := rfl
