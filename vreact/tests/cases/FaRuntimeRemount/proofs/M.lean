import VReact
open VReact

/-! Facts about remounts in the runtime model (attack-1, runtime), checked with the model this
project is verified against. `Child`'s effect is `deps := some []`: React runs it at every mount,
and a changed `key={k}` or a changed enclosing host element (`<div>` → `<section>`) remounts
`<Child />`. -/

/-- A remount is an action of a run: the instance starts again from its element's initial state,
with no recorded dependency arrays and no timers. -/
theorem remount_step {E : Type} (fuel : Nat) (c : CompNode E) (s : c.spec.S) (hinv : c.spec.inv c.d s)
    (deps : Option (List (Option (List DepVal)))) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) :
    ∃ kids', step fuel (.mk c s hinv deps tasks kids) (.remount [])
      = .mk c (c.spec.init c.d c.hpre) (c.spec.init_inv c.d c.hpre) none [] kids' :=
  remount_eq fuel c s hinv deps tasks kids

/-- After a remount, the next flush runs the `[]` effect again, from the initial state, although
it ran before (recorded `some [some []]`, where a flush alone leaves the instance unchanged). -/
theorem empty_deps_rerun_after_remount {E : Type} (fuel : Nat) (rerun : Nat → Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs₀ : (c.render s hinv).effectsOf = [eff]) (hdeps : eff.deps = some [])
    (eff' : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render (c.spec.init c.d c.hpre) (c.spec.init_inv c.d c.hpre)).effectsOf = [eff']) :
    step fuel (.mk c s hinv (some [some []]) tasks kids) (.flush [] rerun false)
        = .mk c s hinv (some [some []]) tasks kids ∧
      (step fuel (step fuel (.mk c s hinv (some [some []]) tasks kids) (.remount [])) (.flush [] rerun false)).stateSigma
        = ⟨c.spec, eff'.setup.apply (c.spec.init c.d c.hpre)⟩ := by
  refine ⟨flushEffects_keeps fuel rerun false c s hinv [] [] tasks kids eff heffs₀ hdeps (by simp [depsChanged]), ?_⟩
  obtain ⟨kids', h⟩ := remount_step fuel c s hinv (some [some []]) tasks kids
  rw [h]
  exact (flushEffects_mount fuel rerun false c _ _ [] kids' eff' heffs).1

/-- The remount of a child is the `remount` action at its instance path. -/
theorem remount_child {E : Type} (fuel : Nat) (i : Inst E) (p : Path) :
    step fuel i (.remount [p]) = i.modifyAt (Inst.remount fuel) [p] := rfl
