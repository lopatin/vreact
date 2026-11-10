import VReact.Budget
import VReact.Tactic
/-! Regression tests for `vreact_ob` (built with the library; the option must be
registered in another module than the one that sets it). -/

/-! Running out of the budget is a failure (a warning, the goal admitted with `sorry`) at that
obligation, and the declaration goes on to elaborate its other obligations (the second
failure). Nothing is an error: the module builds. -/
/--
warning: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
⊢ List.foldl (fun x1 x2 => x1 + x2) 0 (List.range 200) = 19900
---
warning: vreact: second obligation ran
⊢ True
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example : (List.range 200).foldl (· + ·) 0 = 19900 ∧ True :=
  ⟨by vreact_ob decide, by vreact_ob fail "second obligation ran"⟩

-- Ordinary failures are failures too (the failure text shows the goal).
/--
warning: vreact: plain failure
⊢ True
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : True := by vreact_ob fail "plain failure"

-- A proved obligation says so: the report requires this positive evidence.
/-- info: vreact:ok -/
#guard_msgs in
example : 2 + 2 = 4 := by vreact_ob decide

-- Goals left by the automation, and a failure text without a goal (the goal is added).
/--
warning: vreact: unsolved goals
⊢ 1 = 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 1 = 1 := by vreact_ob skip

/--
warning: vreact: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
where
 a := x
⊢ ∀ (x : Int), x < 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∀ x : Int, x < 0 := by vreact_ob omega

/-! The automation cannot fake a proof: `sorry` it produces (directly or through an auxiliary
lemma), an error it logs without failing, and `vreact:` messages it logs (a forged result) are
all caught. -/
open Lean Elab Tactic in
elab "vreact_test_forge" : tactic => do
  logInfo "vreact:ok"
  logWarning "vreact: forged failure"

open Lean Elab Tactic in
elab "vreact_test_log_error" : tactic => do
  logError "logged, not thrown"
  (← getMainGoal).admit

/--
warning: vreact: the automation closed the goal with `sorry`
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : False := by vreact_ob sorry

/--
warning: vreact: the automation closed the goal with `sorry`
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : False := by vreact_ob (vreact_test_forge; sorry)

open Lean Elab Tactic Meta in
elab "vreact_test_aux_sorry" : tactic => do
  let g ← getMainGoal
  let t ← g.getType
  g.assign (← mkAuxTheorem t (← mkSorry t false))

/--
warning: vreact: the automation closed the goal with `sorry`
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : False := by vreact_ob vreact_test_aux_sorry

/--
warning: vreact: logged, not thrown
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : False := by vreact_ob vreact_test_log_error

/-- info: vreact:ok -/
#guard_msgs in
example : True := by vreact_ob (vreact_test_forge; trivial)

/-! `vreact_try` and the alternatives of `vreact_finish` catch runtime exceptions such as
`maximum recursion depth` (to fall back to the next strategy), never the heartbeat limit:
running out of the budget stays a timeout of the obligation. -/
/--
warning: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
⊢ List.foldl (fun x1 x2 => x1 + x2) 0 (List.range 200) = 19900
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example : (List.range 200).foldl (· + ·) 0 = 19900 := by vreact_ob vreact_try decide

/--
warning: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
xs : List Int
_h : xs.length = 3
⊢ 0 < xs.length ∧ List.foldl (fun x1 x2 => x1 + x2) 0 (List.range 200) = 19900
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example (xs : List Int) (_h : xs.length = 3) : 0 < xs.length ∧ (List.range 200).foldl (· + ·) 0 = 19900 := by
  vreact_ob vreact_finish

/-! A proof through a `sorry` from elsewhere proves nothing. When the goal holds the admitted
proof of a false statement (an obligation above that failed) and the automation uses it, or
when the proof unfolds a definition that holds one, the obligation is *blocked*: neither proved
(the first goal is false) nor failed (the second is true). A `sorry` the automation makes is
still a failure. A proof that only refers to another declaration whose proof was admitted is a
proof modulo that declaration's contract: it is proved (and `sorryAx` is in its axioms). (The
declarations are private: the library imports this module.) -/
namespace VReactBudgetTest

/--
warning: vreact: no proof
⊢ 0 > 5
---
warning: vreact:blocked it depends on `sorry` from elsewhere (an obligation that failed, a declaration with an error, or a hole()) that its goal or its proof contains, so this obligation could not be checked on its own; fix that first
its proof uses `sorry` from elsewhere
⊢ ⟨0, ⋯⟩.val > 5
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : (⟨0, by vreact_ob fail "no proof"⟩ : {n : Nat // n > 5}).1 > 5 := by
  vreact_ob exact Subtype.property _

/--
warning: vreact: no proof
xs : List Nat
⊢ 1 < xs.length
---
warning: declaration uses `sorry`
-/
#guard_msgs in
private def second (xs : List Nat) : Nat := xs[1]'(by vreact_ob fail "no proof")

/--
warning: vreact:blocked it depends on `sorry` from elsewhere (an obligation that failed, a declaration with an error, or a hole()) that its goal or its proof contains, so this obligation could not be checked on its own; fix that first
its proof uses `sorry` from elsewhere
x : Nat
⊢ second [x, x + 1] > x
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x : Nat) : second [x, x + 1] > x := by vreact_ob (rw [second]; simp)

/--
warning: vreact: the automation closed the goal with `sorry`
x : Nat
⊢ second [x, x + 1] > x
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x : Nat) : second [x, x + 1] > x := by vreact_ob (rw [second]; sorry)

/--
warning: vreact: no proof
x : Nat
⊢ x > x + 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
private theorem wrong (x : Nat) : x > x + 1 := by vreact_ob fail "no proof"

/-- info: vreact:ok -/
#guard_msgs in
example (y : Nat) : y > y + 1 := by vreact_ob exact wrong y

-- An internal auxiliary lemma (`_auxLemma`, …) is a piece of an earlier proof, not a contract:
-- a proof through one that holds an admitted `sorry` is blocked.
/--
warning: vreact: no proof
⊢ 0 > 5
---
warning: declaration uses `sorry`
-/
#guard_msgs in
private theorem _bt_aux : (0 : Nat) > 5 := by vreact_ob fail "no proof"

/--
warning: vreact:blocked it depends on `sorry` from elsewhere (an obligation that failed, a declaration with an error, or a hole()) that its goal or its proof contains, so this obligation could not be checked on its own; fix that first
its proof uses `sorry` from elsewhere
⊢ 0 > 5
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : (0 : Nat) > 5 := by vreact_ob exact _bt_aux

end VReactBudgetTest
