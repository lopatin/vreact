import Lean
/-!
# `vreact_contracts` — modular reasoning about `@opaque` functions

For every call `f a₁ … aₙ` (no bound variables) occurring in the goal or a
hypothesis, where `f` has proved postconditions `f.post`, `f.post2`, …
(generated from `ensures(…)`), add the instantiated facts `f.post a₁ … aₙ` to
the local context.  The facts are then normalised together with the goal, so
contract and goal always share a normal form.  This is per-call-site contract
instantiation, as in Dafny/Boogie, and avoids global E-matching patterns.

A call under a binder (`∀ s, … f s.x …`, `∃ a, … f a …`, the update `fun τ => … f τ.x …` of a
timer callback) is made closed first by opening the binder (`vreact_open`, below and in
`Tactic.lean`).  A call that stays under a binder — in a quantified hypothesis that `grind`
instantiates itself — gets no contract instance.
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
  -- `vreact_auto` runs this more than once: do not add a fact that is already a hypothesis
  let mut have_ : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail then have_ := have_.push (← instantiateMVars d.type)
  for call in (← calls.get) do
    let .const f us := call.getAppFn | continue
    for thm in contractsOf env f do
      let some ci := env.find? thm | continue
      let pf := mkAppN (mkConst thm us) call.getAppArgs
      -- only if the theorem takes exactly the call's arguments
      let ty ← try inferType pf catch _ => continue
      unless (← isProp ty) do continue
      let _ := ci
      let ty ← instantiateMVars ty
      if have_.contains ty then continue
      have_ := have_.push ty
      g ← g.assert (← mkFreshUserName `hcontract) ty pf
      let (_, g') ← g.intro1P
      g := g'
  replaceMainGoal [g]

elab "vreact_contracts" : tactic => addContractFacts

/-! ### Calls under binders

`vreact_contracts` instantiates a contract only at a *closed* call.  A call of a program function
under a binder of the goal has no actual arguments yet: `bump s.n` under the `∀ s` of a robust
outcome (`Robust`/`RebaseSafe` unfold to `∀ s, inv s → inv (o.apply s)`), `clamp a` under the
`∃ a` that `y ∈ xs.map (fun x => clamp x)` normalises to, `stepFeed τ.sim.feed` in the update
`fun τ => { τ with sim := simReducer τ.sim .tick }` of a timer callback `t` that the goal only
knows by its equation `t = fun _ => …` (a transparent reducer is unfolded into the update).  The
helpers below open such binders with ordinary proof steps (`intro`, `cases`, `subst`), so that the
call becomes closed and `vreact_contracts` adds exactly `f.post` applied to its actual arguments.
They act only where opening the binder makes a call closed (a call in a `match` arm is left to
`split`), so other goals are left as they were. -/

/-- `f a₁ … aₙ` (all arguments) of a program function (`VTS.…`) that has contracts. -/
def isContractCall (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const f _ =>
    (`VTS).isPrefixOf f && !(contractsOf env f).isEmpty &&
      match env.find? f with
      | some fi => e.getAppNumArgs == fi.type.getForallArity
      | none => false
  | _ => false

/-- `e` has a contract call (`isContractCall`) that mentions a variable bound inside `e`. -/
def hasBoundCall (env : Environment) (e : Expr) : Bool :=
  (e.find? fun sub => sub.hasLooseBVars && isContractCall env sub).isSome

/-- The body `b` of a binder, instantiated with a placeholder variable `x`: whether `b` has a
closed contract call of `x` (opening the binder makes that call closed). -/
private def callOfBinder (env : Environment) (b : Expr) : Bool :=
  let x := mkFVar ⟨`_vreact_bound⟩
  let b := b.instantiate1 x
  (b.find? fun sub => !sub.hasLooseBVars && isContractCall env sub && sub.containsFVar x.fvarId!).isSome

/-- `∃ a, …` (also nested) whose body has a contract call of the witness. -/
partial def existsOpens (env : Environment) (e : Expr) : Bool :=
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam _ _ b _ => callOfBinder env b || existsOpens env (b.instantiate1 (mkFVar ⟨`_vreact_bound⟩))
    | _ => false
  else false

/-- Whether `openBoundTarget` opens a binder of the target `e`: a leading `∀ x` whose body has a
contract call of `x`, or an `∃` hypothesis `(∃ a, …) → …` that `existsOpens`; along `∧`. -/
partial def targetOpens (env : Environment) (e : Expr) : Bool :=
  match e with
  | .forallE _ d b _ =>
    callOfBinder env b || existsOpens env d || targetOpens env (b.instantiate1 (mkFVar ⟨`_vreact_bound⟩))
  | _ =>
    if e.isAppOfArity ``And 2 then targetOpens env e.appFn!.appArg! || targetOpens env e.appArg!
    else false

/-- Substitute a function-valued local `t` with its definition `h : t = fun x => …` when the
definition has a contract call under a binder (the timer callbacks of an effect are checked as
`∀ t ∈ [fun _ => …], …`, which normalises to such an equation): afterwards `t e` is the
callback's body, and its updates apply to the state.  `none` if there is none. -/
def substBoundFnEq? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let env ← getEnv
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    for (x, v) in [(lhs, rhs), (rhs, lhs)] do
      unless x.isFVar do continue
      if (← x.fvarId!.getDecl).isLet then continue
      unless (← whnfR (← inferType x)).isForall do continue
      if v.containsFVar x.fvarId! then continue
      unless hasBoundCall env v do continue
      return some (← subst g d.fvarId)
  return none

/-- `cases` a hypothesis `∃ a, …` whose body has a contract call of `a` (`y ∈ xs.map (fun x =>
clamp x)` normalises to `∃ a, a ∈ xs ∧ clamp a = y`): the witness becomes a local.  `none` if
there is none. -/
def casesBoundExists? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let env ← getEnv
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    unless existsOpens env ty do continue
    let x := match ty.appArg! with
      | .lam n .. => n
      | _ => `w
    let #[sg] ← g.cases d.fvarId #[{ varNames := [x, d.userName] }] | continue
    return some sg.mvarId
  return none

/-- Open the goal's binders over contract calls (`targetOpens`): introduce a leading `∀`/`→`, split
a conjunction into its conjuncts — only along the parts that `targetOpens` — and open the `∃`
hypotheses this introduces. -/
partial def openBoundTarget (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let env ← getEnv
  let tgt ← instantiateMVars (← g.getType)
  unless targetOpens env tgt do return [g]
  if tgt.isForall then
    let (_, g) ← g.intro1P
    let mut g := g
    repeat
      let some g' ← casesBoundExists? g | break
      g := g'
    return ← openBoundTarget g
  if tgt.isAppOfArity ``And 2 then
    let [g1, g2] ← g.apply (mkConst ``And.intro) | return [g]
    return (← openBoundTarget g1) ++ (← openBoundTarget g2)
  return [g]

end VReact
