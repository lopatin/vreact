import VReact
open VReact

/-! Facts about StrictMode's double invocation of effects in the runtime model (attack-1,
runtime), checked with the model this project is verified against. `App`'s effect is
`deps := some []`, with the functional update `m => m < 10 ? m + 1 : m`. -/

/-- The application starts with nothing recorded: its first flush is a flush after mounting. -/
theorem start_fresh (fuel : Nat) (root : CompNode Empty) : (start fuel root).depsOf = none := by
  obtain ⟨kids, h⟩ := mount_none fuel root
  simp only [start, h, Inst.depsOf]

/-- At the first flush after mounting, a run may choose StrictMode's double invocation: the
effect's setup is applied twice, with the same closure (React 18 in development: setup, cleanup,
setup), and its timers are registered twice (the model has no cleanup step). -/
theorem strict_mount_runs_twice {E : Type} (fuel : Nat) (rerun : Nat → Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [eff]) :
    (step fuel (.mk c s hinv none tasks kids) (.flush [] rerun true)).stateSigma
        = ⟨c.spec, eff.setup.apply (eff.setup.apply s)⟩ ∧
      (step fuel (.mk c s hinv none tasks kids) (.flush [] rerun true)).timerCount
        = 2 * eff.tasks.length + tasks.length := by
  have h := flushEffects_mount fuel rerun true c s hinv tasks kids eff heffs
  exact ⟨h.1, h.2.1⟩

/-- …or not (production, or no StrictMode): the setup is applied once. -/
theorem mount_runs_once {E : Type} (fuel : Nat) (rerun : Nat → Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [eff]) :
    (step fuel (.mk c s hinv none tasks kids) (.flush [] rerun false)).stateSigma
        = ⟨c.spec, eff.setup.apply s⟩ :=
  (flushEffects_mount fuel rerun false c s hinv tasks kids eff heffs).1

/-- The double invocation happens only at mount: once the `[]` array is recorded, a flush leaves
the instance unchanged whatever the run chooses. -/
theorem strict_only_at_mount {E : Type} (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (eff : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [eff]) (hdeps : eff.deps = some []) :
    step fuel (.mk c s hinv (some [some []]) tasks kids) (.flush [] rerun strict)
      = .mk c s hinv (some [some []]) tasks kids :=
  flushEffects_keeps fuel rerun strict c s hinv [] [] tasks kids eff heffs hdeps (by simp [depsChanged])

/-- The effect's update, applied twice from 0 (one queue: the second setup's update follows the
first's), gives 2, as in React. -/
example : (Outcome.mk (E := Empty) [fun (m : Int) => if m < 10 then m + 1 else m] none).apply
    ((Outcome.mk (E := Empty) [fun (m : Int) => if m < 10 then m + 1 else m] none).apply 0) = 2 := by
  decide
