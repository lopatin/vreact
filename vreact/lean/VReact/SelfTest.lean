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

end VReact.SelfTest
