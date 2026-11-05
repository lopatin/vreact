import Lean
/-!
# `vreact_contracts` — modular reasoning about `@opaque` functions

For every call `f a₁ … aₙ` (no bound variables) occurring in the goal or a
hypothesis, where `f` has proved postconditions `f.post`, `f.post2`, …
(generated from `ensures(…)`), add the instantiated facts `f.post a₁ … aₙ` to
the local context.  The facts are then normalised together with the goal, so
contract and goal always share a normal form.  This is per-call-site contract
instantiation, as in Dafny/Boogie, and avoids global E-matching patterns.
-/
namespace VReact
open Lean Meta Elab Tactic

/-- The postcondition theorems generated for function `f`. -/
def contractsOf (env : Environment) (f : Name) : List Name :=
  let names := (List.range 8).map (fun k => if k == 0 then f ++ `post else f ++ Name.mkSimple s!"post{k + 1}")
  names.filter env.contains

def addContractFacts : TacticM Unit := withMainContext do
  let env ← getEnv
  let goal ← getMainGoal
  let mut targets : Array Expr := #[← instantiateMVars (← goal.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then targets := targets.push (← instantiateMVars d.type)
  let lctx ← getLCtx
  let calls ← IO.mkRef (#[] : Array Expr)
  for t in targets do
    forEachExpr t fun sub => do
      if sub.hasLooseBVars || sub.hasMVar then return
      -- binders visited by `forEachExpr` become temporary fvars: only use closed calls
      if sub.hasAnyFVar (fun fv => !lctx.contains fv) then return
      if let .const f _ := sub.getAppFn then
        if !(contractsOf env f).isEmpty then
          let some fi := env.find? f | return
          if sub.getAppNumArgs != fi.type.getForallArity then return
          let cs ← calls.get
          unless cs.any (· == sub) do calls.set (cs.push sub)
  let mut g := goal
  for call in (← calls.get) do
    let .const f us := call.getAppFn | continue
    for thm in contractsOf env f do
      let some ci := env.find? thm | continue
      let pf := mkAppN (mkConst thm us) call.getAppArgs
      -- only if the theorem takes exactly the call's arguments
      let ty ← try inferType pf catch _ => continue
      unless (← isProp ty) do continue
      let _ := ci
      g ← g.assert (← mkFreshUserName `hcontract) ty pf
      let (_, g') ← g.intro1P
      g := g'
  replaceMainGoal [g]

elab "vreact_contracts" : tactic => addContractFacts

end VReact
