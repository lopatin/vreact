import VReact.Tactic
/-! Regression tests for `vreact_auto` itself (built with the library). -/
namespace VReact.SelfTest
open VReact

structure St where
  count : Int
  name : JS.Str

@[vreact_simp] def inv (s : St) : Prop := 0 ≤ s.count ∧ JS.strLen s.name ≤ 10

example (s : St) (h : inv s) : inv ((Outcome.mk (E := Empty) [fun t => { t with count := s.count + 1 }] none).apply s) := by
  vreact_auto
example (s : St) (h : inv s) (v : JS.Str) :
    inv ((if JS.strLen v ≤ 10 then Outcome.mk (E := Empty) [fun t => { t with name := v }] none else Outcome.mk [] none).apply s) := by
  vreact_auto
example (a : Int) (h : a % 2 = 0) : JS.rem (a + 2) 2 (by decide) = 0 := by vreact_auto
example (s : JS.Str) (h : JS.strLen (JS.trim s) ≠ 0) : 0 < JS.strLen (JS.trim s) := by vreact_auto
example (xs : List Int) (n : Int) (h : 0 ≤ n) : (JS.slice xs 0 (some n)).length ≤ n := by
  simp [JS.slice, JS.relIndex]; omega

example : JS.strLen (JS.Str.ofString "Write the spec") = 14 := by vreact_auto
example : JS.Str.ofString "a" ≠ JS.Str.ofString "b" := by vreact_auto
example : JS.strLen (JS.Str.ofString "😀") = 2 := by vreact_auto

-- `vreact_noemit` (emit-freedom of robust handlers / effect setups), incl. `if` and `let`
example (b : Bool) : (if h : b = true then Outcome.mk (S := St) (E := Empty) [] none
    else Outcome.mk [fun t => { t with count := 1 }] none).emit = none := by vreact_noemit
example : ∀ (e : DomEvent), ((fun (_ : DomEvent) => let c := (3 : Int);
    if c < 2 then Outcome.mk (S := St) (E := Empty) [] none else Outcome.mk [] none) e).emit = none := by
  vreact_noemit
example : (Outcome.mk (S := St) (E := Empty) [] none).emit = none := by vreact_noemit
example (s : St) (xs : List Int) : True := by
  let c := s.count  -- a render-local discriminant
  have : ∀ (_ : DomEvent), (match h : xs.find? (fun x => x == c) with
      | some v => if v < c then Outcome.mk (S := St) (E := Empty) [fun t => { t with count := v }] none
                  else Outcome.mk [] none
      | none => Outcome.mk [] none).emit = none := by vreact_noemit
  trivial

/-! ### `toSorted` (#10, #55): the order of an inconsistent comparator is not fixed -/

-- the proofs that used to show the model's (non-V8) tie order no longer go through
example : True := by
  fail_if_success
    (have : JS.toSorted [(1 : Int), 2] (fun _ _ => (1 : Int)) = [2, 1] := by
      simp [JS.toSorted, List.mergeSort])
  fail_if_success
    (have : ∀ (a b : Int) (cmp : Int → Int → Int), JS.toSorted [a, b] cmp = if cmp a b ≤ 0 then [a, b] else [b, a] := by
      intro a b cmp; unfold JS.toSorted; by_cases h : cmp a b ≤ 0 <;> simp [h, List.mergeSort, List.merge])
  trivial
-- the specification of `unspecifiedSort` admits both engines' results
example : ∃ f : List Int → (Int → Int → Int) → List Int, (∀ xs cmp, (f xs cmp).Perm xs) ∧ f [1, 2] (fun _ _ => 1) = [1, 2] :=
  ⟨fun xs _ => xs, fun _ _ => List.Perm.refl _, rfl⟩
example : ∃ f : List Int → (Int → Int → Int) → List Int, (∀ xs cmp, (f xs cmp).Perm xs) ∧ f [1, 2] (fun _ _ => 1) = [2, 1] :=
  ⟨fun xs _ => xs.reverse, fun _ _ => List.reverse_perm _, rfl⟩
-- a consistent comparator: the (unique) stable sort
example : JS.toSorted [(2 : Int), 1] (fun a b => a - b) = [1, 2] := by
  rw [JS.toSorted_of_consistent (JS.consistent_sub (fun x => x) _)]; simp
example (xs : List St) (h : (xs.map (·.count)).Nodup) (hx : xs ≠ []) :
    ((JS.toSorted xs (fun a b => if a.count < b.count then -1 else 1)).map (·.count)).Nodup ∧
      0 < (JS.toSorted xs (fun a b => if a.count < b.count then -1 else 1)).length := by
  vreact_auto

/-! ### list facts (#16, #46, #47, #61, #62, #63) -/

example (xs : List JS.Str) (q : JS.Str) (h : 0 ≤ JS.indexOf xs q) : JS.indexOf xs q < xs.length := by vreact_auto
example (xs : List JS.Str) (q : JS.Str) (h : 0 ≤ JS.indexOf xs q) (h' : (JS.indexOf xs q).toNat < xs.length) :
    xs[(JS.indexOf xs q).toNat] = q := by vreact_auto
example (xs : List Int) (i : Int) (h : 0 ≤ i ∧ i + 1 < xs.length) :
    (JS.withAt (JS.withAt xs i 0 (by omega)) (i + 1) 1 (by simp; omega)).length = xs.length := by vreact_auto
example (xs : List St) (a : Int) (b : Option Int) (h : (xs.map (·.count)).Nodup) :
    ((JS.slice xs a b).map (·.count)).Nodup := by vreact_auto
example (xs : List Int) (x : Int) (h : x ∈ JS.slice xs 1) : x ∈ xs := by vreact_auto
example : (List.map (fun i => Key.int i) (JS.range 5)).Nodup := by vreact_auto
example (xs : List St) (p : St → Bool) (h : (xs.filter p).length ≤ 5) (k : Int) :
    ((xs.filter (fun s => !JS.eq s.count k)).filter p).length ≤ 5 := by vreact_auto
example (xs : List St) (h : (xs.filter (fun s => !JS.eq s.count 0)).length ≤ 5) :
    ((xs.map (fun s => { s with count := 0 })).filter (fun s => !JS.eq s.count 0)).length = 0 := by vreact_auto

/-! ### automation shape (#40, #57, #58, #65) -/

@[vreact_simp] def three (xs : List Int) : Prop := xs.length = 3

-- a `let` whose value holds a proof built from `h` must not keep `h` folded
example (xs : List Int) (h : three xs) :
    let x := JS.get xs 0 (by unfold three at h; omega); 0 < xs.length ∧ x = x := by vreact_auto

-- record fields through a `dite` whose condition simp rewrites (no stale-instance failure)
example (s : St) (xs : List Int) :
    (if h : JS.le 0 (JS.len xs) = true then { s with count := 1 } else s).name = s.name := by vreact_auto

-- a failure reports the goal, not `simp_all made no progress`
open Lean Elab Tactic Meta in
elab "vreact_fails_showing_goal " t:term : tactic => do
  let p ← Term.elabTermAndSynthesize t (some (mkSort .zero))
  let g ← mkFreshExprMVar p
  let saved ← saveState
  setGoals [g.mvarId!]
  let res ← try withoutRecover (evalTactic (← `(tactic| vreact_auto))); pure none
    catch e => pure (some (← e.toMessageData.toString))
  saved.restore
  match res with
  | none => throwError "vreact_auto proved a false goal"
  | some msg => unless (msg.splitOn "⊢").length > 1 do throwError "the failure shows no goal: {msg}"

example : True := by
  vreact_fails_showing_goal (∀ (a d : Int) (h : d ≠ 0), JS.rem a d h = a)
  vreact_fails_showing_goal (∀ (xs : List Int) (i : Int), 0 ≤ i ∧ i < xs.length)
  trivial

end VReact.SelfTest
