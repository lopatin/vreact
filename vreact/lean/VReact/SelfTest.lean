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

/-! ### runtime exceptions of `grind` fall back (Au A1) -/

-- `grind` raises `maximum recursion depth` on this hypothesis shape (a dependent binder with a
-- literal `Int` bound, as `forall(0, 3, i => xs[i] >= 0)` produces); the obligation must still be
-- proved by a later alternative (`omega` on the unpacked guard), not fail with the exception.
example (xs : List Int)
    (h : ∃ (_ : (xs.length : Int) = 3), ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 3), xs[i.toNat]'(by omega) ≥ 0) :
    0 ≤ (1 : Int) ∧ (1 : Int) < xs.length := by
  vreact_auto
example (xs : List Int)
    (h : ∃ (_ : (xs.length : Int) = 3), ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 3), xs[i.toNat]'(by omega) ≥ 0) :
    True := by
  vreact_try grind  -- (`try grind` would abort the declaration)
  trivial

/-! ### literal strings, `indexOf`/`findIndex` ranges, swaps (Au A2) -/

example : JS.Str.ofString "Hello, " ++ JS.Str.ofString "world" = JS.Str.ofString "Hello, world" := by vreact_auto
example (s : JS.Str) : s ++ JS.Str.ofString "a" ++ JS.Str.ofString "b" = s ++ JS.Str.ofString "ab" := by vreact_auto
example : JS.Str.ofString "n=" ++ JS.str (7 : Int) = JS.Str.ofString "n=7" := by vreact_auto
example : JS.str (-12 : Int) ++ JS.str true = JS.Str.ofString "-12true" := by vreact_auto
example : JS.Str.ofString "a" ++ JS.Str.ofString "b" ≠ JS.Str.ofString "ba" := by vreact_auto
example (xs : List Int) (v : Int) : JS.indexOf xs v ≥ -1 := by vreact_auto
example (xs : List St) (p : St → Bool) : -1 ≤ JS.findIndex xs p ∧ JS.findIndex xs p < xs.length := by vreact_auto
-- the range facts reach `omega` too (contracts of `indexOf`/`findIndex`)
example (xs : List Int) (v : Int) : JS.indexOf xs v + 1 ≤ xs.length := by
  vreact_contracts; omega
example (xs : List St) (i j : Int) (hi : 0 ≤ i ∧ i < xs.length) (hj : 0 ≤ j ∧ j < xs.length)
    (h : (xs.map (·.count)).Nodup) :
    ((JS.withAt (JS.withAt xs i (JS.get xs j hj) hi) j (JS.get xs i hi) (by simp; omega)).map (·.count)).Nodup := by
  vreact_auto
example (xs : List Int) (i : Int) (hi : 0 ≤ i ∧ i + 1 < xs.length) (h : xs.Nodup) :
    (JS.withAt (JS.withAt xs i (JS.get xs (i + 1) (by omega)) (by omega)) (i + 1) (JS.get xs i (by omega))
      (by simp; omega)).Nodup := by
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

/-! ### round 3 (Lx): chains, counts by key, `%`, enumerations, bounded quantifiers, literals -/

-- distinct keys through a chain of list operations (`vreact_subperm`)
example (xs : List St) (h : (xs.map (·.count)).Nodup) (c : St → St → Int) (p : St → Bool) :
    (((JS.slice (JS.toSorted xs c) 1 (some 5)).filter p).reverse.map (·.count)).Nodup := by vreact_auto
-- deleting by the key of a present element of a list with distinct keys removes one
example (xs : List St) (i : Nat) (hi : i < xs.length) (h : (xs.map (·.count)).Nodup) :
    (xs.filter (fun s => !JS.eq s.count (xs[i]'hi).count)).length + 1 = xs.length := by vreact_auto
-- a map-update by key changes a count by at most one
example (xs : List St) (k : Int) (h : (xs.map (·.count)).Nodup) :
    ((xs.map (fun s => if s.count = k then { s with name := JS.Str.ofString "x" } else s)).filter
      (fun s => JS.eq s.name (JS.Str.ofString "x"))).length ≤ (xs.filter (fun s => JS.eq s.name (JS.Str.ofString "x"))).length + 1 := by
  vreact_auto
-- `%` with a variable divisor
example (s n : Int) (hn : 0 < n) (hs : 0 ≤ s) : 0 ≤ JS.rem s n (by omega) ∧ JS.rem s n (by omega) < n := by vreact_auto
-- a disjunction over an enumeration (case split fallback)
inductive Color where | red | green | blue
deriving DecidableEq
example (c : Color) : (c = .red ∧ (if c = .red then (1 : Int) else 0) = 1) ∨ (c = .green ∨ c = .blue) := by vreact_auto
-- a bounded quantifier with a numeral bound, at numeral indices
example (xs : List Int)
    (h : ∃ (_ : (xs.length : Int) = 3), ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 3), xs[i.toNat]'(by omega) ≥ 0) :
    xs[0]'(by obtain ⟨_, _⟩ := h; omega) + xs[2]'(by obtain ⟨_, _⟩ := h; omega) ≥ 0 := by
  vreact_auto
-- literal strings
example : JS.strIncludes (JS.Str.ofString "a@b") (JS.Str.ofString "@") = true := by vreact_auto
example : JS.startsWith (JS.Str.ofString "ab") (JS.Str.ofString "b") = false := by vreact_auto

/-! ### round 3 repairs (Lx): copies of guarded preconditions, `!==` updates, exact `%`,
nested enums, maps in key chains, bounded goals -/

-- a single guarded precondition the goal depends on: its `vreact_expose` copy must survive
@[vreact_simp, reducible] def exLenT (xs : List Int)
    (_h : ∃ i : Int, ∃ (h₁ : 0 ≤ i ∧ i < (xs.length : Int)), JS.get xs i h₁ < 0) : Int := xs.length
example (xs : List Int) (h : ∃ i : Int, ∃ (h₁ : 0 ≤ i ∧ i < (xs.length : Int)), JS.get xs i h₁ < 0) :
    exLenT xs h > 0 := by vreact_auto
-- a map-update guarded by a negated key test
example (xs : List St) (k : Int) (h : (xs.map (·.count)).Nodup) :
    ((xs.map (fun s => if ¬ s.count = k then s else { s with name := JS.Str.ofString "x" })).filter
      (fun s => JS.eq s.name (JS.Str.ofString "x"))).length ≤ (xs.filter (fun s => JS.eq s.name (JS.Str.ofString "x"))).length + 1 := by
  vreact_auto
-- exact values of `%`
example (n : Int) (hn : 0 < n) : JS.rem n n (by omega) = 0 := by vreact_auto
example (s n : Int) (hn : 0 < n) (hs : 0 ≤ s ∧ s + 1 < n) : JS.rem (s + 1) n (by omega) = s + 1 := by vreact_auto
-- an enumeration that is a field of a field
structure Box where
  c : Color
  k : Int
structure Box2 where
  b : Box
example (o : Box2) : (o.b.c = .red ∧ (if o.b.c = .red then (1 : Int) else 0) = 1) ∨ (o.b.c = .green ∨ o.b.c = .blue) := by
  vreact_auto
-- distinct keys through a map that keeps the key
example (xs : List St) (h : (xs.map (·.count)).Nodup) :
    ((JS.slice (xs.map (fun s => { s with name := JS.Str.ofString "x" })) 0 (some 3)).map (·.count)).Nodup := by
  vreact_auto
example (xs : List St) (k : Int) (h : (xs.map (·.count)).Nodup) :
    ((JS.slice (xs.map (fun s => if s.count = k then { s with name := JS.Str.ofString "x" } else s)) 0 (some 3)).map (·.count)).Nodup := by
  vreact_auto
-- a bounded quantifier to establish under a guard, with a two-sided body, and above 8 values
example (xs : List Int) (k : Int) (hl : (xs.length : Int) = 9) (hk : 0 ≤ k ∧ k < 9)
    (h : ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 9), 0 ≤ xs[i.toNat]'(by omega) ∧ xs[i.toNat]'(by omega) ≤ 2) :
    ∃ (h : ((xs.set k.toNat 1).length : Int) = 9), ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 9),
      0 ≤ (xs.set k.toNat 1)[i.toNat]'(by omega) ∧ (xs.set k.toNat 1)[i.toNat]'(by omega) ≤ 2 := by
  vreact_auto
example : ∃ (h : ([0, 0, 0, 0, 0, 0, 0, 0, 0] : List Int).length = 9), ∀ i : Int, ∀ (h₁ : 0 ≤ i) (h₂ : i < 9),
    0 ≤ ([0, 0, 0, 0, 0, 0, 0, 0, 0] : List Int)[i.toNat]'(by simp; omega) := by
  vreact_auto


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

-- round 3 (Lx): the new facts do not prove false goals
example : True := by
  vreact_fails_showing_goal (∀ (xs : List St) (i : Nat) (hi : i < xs.length),
    (xs.filter (fun s => !JS.eq s.count (xs[i]'hi).count)).length + 1 = xs.length)
  vreact_fails_showing_goal (∀ (s n : Int) (h : n ≠ 0), 0 ≤ JS.rem s n h)
  vreact_fails_showing_goal (∀ (c : Color), c = .red ∨ c = .green)
  trivial

-- round 3 repairs (Lx): the new facts do not prove false goals
example : True := by
  vreact_fails_showing_goal (∀ (n : Int) (h : n ≠ 0), JS.rem n n h = 1)
  vreact_fails_showing_goal (∀ (s n : Int) (h : n ≠ 0), JS.rem (s + 1) n h = s + 1)
  vreact_fails_showing_goal (∀ (xs : List St), (xs.map (·.count)).Nodup →
    ((JS.slice (xs.map (fun s => { s with count := 0 })) 0 (some 3)).map (·.count)).Nodup)
  vreact_fails_showing_goal (∀ (o : Box2), o.b.c = .red ∨ o.b.c = .green)
  trivial

-- round 4 (Rl): numbers are opaque — congruence works, nothing is computed or decided
example (x : JS.Num) (k : Int) :
    JS.eq (JS.Num.lt x (JS.Num.ofInt k)) (JS.Num.lt x (JS.Num.ofInt k)) = true := by vreact_auto
example (x y : JS.Num) (h : JS.Num.lt x y = true) : JS.Num.lt x y = true := by vreact_auto
example : True := by
  -- `===` is not reflexive (NaN)
  vreact_fails_showing_goal (∀ (x : JS.Num), JS.Num.eq x x = true)
  -- `Math.max(1, NaN)` is NaN (Lean's `max` on Float is 1)
  vreact_fails_showing_goal (JS.Num.eq (JS.Num.max 1 (JS.Num.ofInt 0 / JS.Num.ofInt 0)) 1 = true)
  -- no arithmetic on literals
  vreact_fails_showing_goal (JS.Num.eq ((0.1 : JS.Num) + 0.2) 0.30000000000000004 = true)
  vreact_fails_showing_goal ((0.1 : JS.Num) + 0.2 = 0.30000000000000004)
  -- `<`, `<=`, `===` are unrelated; rounding functions are unrelated
  vreact_fails_showing_goal (∀ (x y : JS.Num), JS.Num.lt x y = true → JS.Num.le x y = true)
  vreact_fails_showing_goal (∀ (x : JS.Num), JS.Num.round x = JS.Num.floor (x + 0.5))
  vreact_fails_showing_goal (∀ (x : JS.Num), JS.Num.trunc x = JS.Num.round x)
  trivial

end VReact.SelfTest
