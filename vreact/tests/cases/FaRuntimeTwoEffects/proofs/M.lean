import VReact
open VReact

/-! Facts about a flush of a two-effect component in the runtime model (attack-1, runtime),
checked with the model this project is verified against. `App`'s effects are
`deps := some [VReact.DepVal.int a]` and `deps := some [VReact.DepVal.int b]`. -/

/-- `a` changed 1 → 2, `b` stayed 5: only the first effect runs (compared with effect 0's
recorded array, `[5]` would differ from `[1]` and the second would run too). -/
theorem only_first_reruns {E : Type} (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (e₀ e₁ : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [e₀, e₁]) (h₀ : e₀.deps = some [.int 2])
    (h₁ : e₁.deps = some [.int 5]) :
    (step fuel (.mk c s hinv (some [some [.int 1], some [.int 5]]) tasks kids) (.flush [] rerun strict)).stateSigma
        = ⟨c.spec, e₀.setup.apply s⟩ ∧
      (step fuel (.mk c s hinv (some [some [.int 1], some [.int 5]]) tasks kids) (.flush [] rerun strict)).timerCount
        = e₀.tasks.length + tasks.length :=
  flushEffects_first_of_two fuel rerun strict c s hinv [.int 1] [.int 5] [.int 2] [.int 5] tasks kids e₀ e₁
    heffs h₀ h₁ (by cases rerun 0 <;> decide) (by cases rerun 1 <;> decide)

/-- `a` stayed 2, `b` changed 4 → 5: only the second effect runs. -/
theorem only_second_reruns {E : Type} (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (e₀ e₁ : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [e₀, e₁]) (h₀ : e₀.deps = some [.int 2])
    (h₁ : e₁.deps = some [.int 5]) :
    (step fuel (.mk c s hinv (some [some [.int 2], some [.int 4]]) tasks kids) (.flush [] rerun strict)).stateSigma
        = ⟨c.spec, e₁.setup.apply s⟩ := by
  have hc₀ : depsChanged [.int 2] [.int 2] (rerun 0) = false := by cases rerun 0 <;> decide
  have hc₁ : depsChanged [.int 4] [.int 5] (rerun 1) = true := by cases rerun 1 <;> decide
  simp [step, Inst.modifyAt, flushEffects, flushRuns, heffs,
    firingFrom_two rerun e₀ e₁ [.int 2] [.int 4] [.int 2] [.int 5] h₀ h₁, hc₀, hc₁, runRobust, Inst.stateSigma]

/-- Neither changed: no effect runs; the instance keeps its state, timers and children (a model
that compared effect 1 with effect 0's `[2]` would run it). -/
theorem none_reruns {E : Type} (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) (e₀ e₁ : Effect c.spec.S E (c.spec.inv c.d))
    (heffs : (c.render s hinv).effectsOf = [e₀, e₁]) (h₀ : e₀.deps = some [.int 2])
    (h₁ : e₁.deps = some [.int 5]) :
    step fuel (.mk c s hinv (some [some [.int 2], some [.int 5]]) tasks kids) (.flush [] rerun strict)
      = .mk c s hinv (some [some [.int 2], some [.int 5]]) tasks kids := by
  have hc₀ : depsChanged [.int 2] [.int 2] (rerun 0) = false := by cases rerun 0 <;> decide
  have hc₁ : depsChanged [.int 5] [.int 5] (rerun 1) = false := by cases rerun 1 <;> decide
  simp [step, Inst.modifyAt, flushEffects, flushRuns, heffs, h₀, h₁,
    firingFrom_two rerun e₀ e₁ [.int 2] [.int 5] [.int 2] [.int 5] h₀ h₁, hc₀, hc₁]
