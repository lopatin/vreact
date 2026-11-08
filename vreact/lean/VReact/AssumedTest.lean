import VReact.Assumed
import VReact.Attr
import VReact.Budget
import VReact.BudgetTest
import VReact.Contracts
import VReact.Core
import VReact.JS
import VReact.Lists
import VReact.Normalize
import VReact.Runtime
import VReact.SelfTest
import VReact.Simprocs
import VReact.Tactic
/-! Checks for `vreact_assume` and `#vreact_assumed` (built with the library; the end-to-end
cases are the regression suite's `GxAssume…` cases, where user proofs are separate modules).

The rest of the library uses `VReact.assumed` nowhere but in its declaration (checked first),
so every use in an item's cone comes from the generated code — an `assume(…)` of the program —
or from a user proof, which `#vreact_assumed` names. The declarations below use it only for
facts that are true (they are part of the library: a user proof could name them). -/
namespace VReact.AssumedTest
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut uses : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if env.header.moduleNames[i].getRoot != `VReact then continue
    for n in env.header.moduleData[i]!.constNames do
      if n == ``VReact.assumed then continue
      if let some ci := env.find? n then
        if ci.getUsedConstantsAsSet.contains ``VReact.assumed then uses := uses.push n
  unless uses.isEmpty do
    throwError "the VReact library uses VReact.assumed (reserved for assume(…) in generated code) in {uses.toList}"

-- A library theorem's cone (the whole runtime model): no such use.
/-- info: 'VReact.run_allInv' uses VReact.assumed outside the generated code: [] -/
#guard_msgs in
#vreact_assumed VReact.run_allInv

-- Declarations of the current file stand for generated code (the command is written only at the
-- end of generated files): their own use is the program's `assume(…)`.
theorem fromAssume (x : Int) : x = x := (have _h : x = x := VReact.assumed; rfl)
/-- info: 'VReact.AssumedTest.fromAssume' uses VReact.assumed outside the generated code: [] -/
#guard_msgs in
#vreact_assumed fromAssume

-- A name that does not resolve: no report (its `#print axioms` fails as well).
#guard_msgs in
#vreact_assumed noSuchDeclaration

-- `vreact_assume` assumes the fact under the hypotheses in scope: the auxiliary theorem Lean
-- makes of it (a constant user proofs can name) carries the precondition and the path to the
-- `assume`, not only the variables of the fact. (With `VReact.assumed` at the fact alone, the
-- first would be `∀ xs flag, flag = true ∧ 2 < xs.length`, false for `flag := false`.)
def pick (xs : List Int) (flag : Bool) (h_pre : xs.length > 2) : Int :=
  if h₁ : flag = true then
    have h : flag = true ∧ 2 < xs.length := (by vreact_assume)
    xs[0]'(by omega)
  else 0
/--
info: pick._proof_2 : ∀ (xs : List Int) (flag : Bool), xs.length > 2 → flag = true → flag = true ∧ 2 < xs.length
-/
#guard_msgs in
#check @pick._proof_2
-- (a proved fact in scope is left out: it follows from the hypotheses that are kept)
def afterHave (x : Int) (h_pre : 0 < x) : Int :=
  have h₀ : 0 ≤ x := by omega
  have h : 0 < x := (by vreact_assume)
  x
/-- info: afterHave._proof_3 : ∀ (x : Int), 0 < x → 0 < x -/
#guard_msgs in
#check @afterHave._proof_3

end VReact.AssumedTest
