import VReact.Budget
import VReact.Tactic
/-! Regression tests for `vreact_ob` (built with the library; the option must be
registered in another module than the one that sets it). -/

/-! Running out of the budget is an error at that obligation, and the declaration
goes on to elaborate its other obligations (the second error). -/
/--
error: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
---
error: second obligation ran
⊢ True
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example : (List.range 200).foldl (· + ·) 0 = 19900 ∧ True :=
  ⟨by vreact_ob decide, by vreact_ob fail "second obligation ran"⟩

-- Ordinary failures pass through unchanged.
/--
error: plain failure
⊢ True
-/
#guard_msgs in
example : True := by vreact_ob fail "plain failure"

example : 2 + 2 = 4 := by vreact_ob decide

/-! `vreact_try` and the alternatives of `vreact_finish` catch runtime exceptions such as
`maximum recursion depth` (to fall back to the next strategy), never the heartbeat limit:
running out of the budget stays a timeout of the obligation. -/
/--
error: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example : (List.range 200).foldl (· + ·) 0 = 19900 := by vreact_ob vreact_try decide

/--
error: vreact: (deterministic) timeout: the automation did not finish within this obligation's budget of 1 heartbeats (set "heartbeats" in vreact.json to change it)
-/
#guard_msgs in
set_option vreact.heartbeats 1 in
example (xs : List Int) (h : xs.length = 3) : 0 < xs.length ∧ (List.range 200).foldl (· + ·) 0 = 19900 := by
  vreact_ob vreact_finish
