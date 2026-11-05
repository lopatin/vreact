import VReact.Core
import VReact.Attr
import VReact.Lists
import VReact.Contracts
import VReact.Simprocs
/-!
# `vreact_auto` — the default discharger for every generated proof obligation

1. introduce binders, unfold generated definitions and the model
   (`@[vreact_simp]`), and let-bound locals (`zetaDelta`); hypotheses that a
   local depends on are copied first so that they are unfolded too (`vreact_expose`);
   record fields are pushed through conditionals (`pushProjIte`) and Bool
   `if`-chains become propositions, so a map-update that leaves a field alone leaves
   facts about that field syntactically unchanged;
2. split `if`/`match` in the goal, normalise again;
3. close each case with `grind` (congruence closure + E-matching + linear
   integer arithmetic + case splitting) or `omega`; if both fail on a
   conjunction, prove the conjuncts separately; on a goal that is not a
   conjunction, fall back to `simp_all` variants (also on the parts of guarded
   contracts `∃ (h : a), b h`, `vreact_unpack`); a failure reports `grind`'s
   goal (`vreact_finish`).  Every alternative runs under `tryTactic`: a runtime
   exception such as `maximum recursion depth` (which `first`/`try` let
   through) makes it fail like any other error — except the heartbeat limit,
   `vreact_ob`'s per-obligation budget, which is passed on.

The normalisation set is the simp attribute `vreact_simp` (so a typo in a lemma
name is a build error of this library, never a silent weakening of the tactic).
Users extend the automation by tagging their lemmas `@[vreact_simp]` (rewrite
rules) or `@[grind]`/`grind_pattern` (E-matching facts), or by adding
`macro_rules` for `vreact_auto`.
-/
namespace VReact

-- The model: queue semantics, robustness, emits, keyed lists.
attribute [vreact_simp] Outcome.apply Outcome.apply_nil Outcome.apply_cons Robust Emit KList.ofList
  nodup_map_key_int nodup_map_key_str
-- JS runtime: definitions with exact semantics are unfolded for the decision procedures.
attribute [vreact_simp] JS.lt_iff JS.le_iff JS.eq_iff JS.nodupB_iff JS.lt_false JS.le_false JS.eq_false
  JS.nodupB_false
attribute [vreact_simp] JS.len_eq JS.strLen_eq JS.Str.ofString_empty JS.Str.units_append JS.rem
  JS.floorDiv JS.truncDiv JS.strSlice JS.slice_length JS.relIndex JS.distinct JS.get_eq JS.mem_rangeFrom JS.mem_range JS.abs JS.sign
-- Logic / Bool / lists.
attribute [vreact_simp] dite_eq_ite List.foldl_cons List.foldl_nil decide_eq_true_eq decide_eq_false_iff_not
  Bool.and_eq_true Bool.or_eq_true Bool.not_eq_true' Bool.not_eq_eq_eq_not Bool.not_true ne_eq
  List.map_map Function.comp_def List.map_cons List.map_nil List.all_eq_true List.any_eq_true
  beq_iff_eq List.mem_cons List.not_mem_nil Int.natAbs_natCast
  Option.isSome_iff_ne_none Option.isNone_iff_eq_none List.find?_eq_none Option.some_ne_none
  Option.isSome_some Option.isSome_none Option.isNone_some Option.isNone_none
  forall_eq_or_imp exists_eq_or_imp List.length_cons List.length_nil List.length_append forall_eq exists_eq_left
  or_false false_or or_assoc and_true true_and not_false_eq_true forall_const implies_true false_implies
  not_true_eq_false and_false false_and
-- conditional record updates (`pushProjIte` in `Simprocs.lean`) collapse field by field
attribute [vreact_simp] ite_self

-- Bool `if`-chains (`a && b` / `a || b` with narrowing compile to `if a then b else false`)
-- become propositions, so that invariants are conjunctions in hypotheses and goals.
attribute [vreact_simp] Bool.ite_eq_true_distrib Bool.ite_eq_false_distrib ite_false_right ite_false_left
  ite_true_left ite_true_right Bool.false_eq_true

open Lean Meta Elab Tactic in
/-- `simp … at *` skips hypotheses that other locals or the goal depend on.  A render-level
`const cur = xs[i]` is `let cur := JS.get xs i (proof)`, and that proof uses the
invariant `hinv` (or the precondition `hpre`), so `hinv` would stay folded for every
later obligation; likewise a handler whose outcome indexes (`items[sel].id` in a
`filter`) has that proof in its goal.  Add a copy of each such hypothesis; `simp`
normalises the copy. -/
elab "vreact_expose" : tactic => withMainContext do
  let decls := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
  let mut g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  for d in decls do
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let mut used := tgt.containsFVar d.fvarId
    for d' in decls do
      if d'.index ≤ d.index then continue
      if (← instantiateMVars d'.type).containsFVar d.fvarId then used := true; break
      if let some v := d'.value? then
        if (← instantiateMVars v).containsFVar d.fvarId then used := true; break
    if used then
      (_, g) ← (← g.assert d.userName ty (mkFVar d.fvarId)).intro1P
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Run `tac` like an alternative of `first` (no error recovery); if it fails, restore the
state and return the exception.  Unlike `first`/`try`, this also catches *runtime*
exceptions other than the heartbeat limit: `grind` and `simp` can run into
`maximum recursion depth` (e.g. Lean's arithmetic normaliser under a binder
`∀ (h : i < 3), … xs[i.toNat]'h …`, the shape of `forall(0, 3, i => xs[i] …)`), and that
must make us try the next strategy, not abort the obligation.  The heartbeat limit is
passed on: it is `vreact_ob`'s per-obligation budget, and running out of it is reported
as a timeout of the obligation (interrupts are passed on by `tryCatchRuntimeEx`). -/
def tryTactic (tac : TacticM Unit) : TacticM (Option Exception) := do
  let s ← saveState
  tryCatchRuntimeEx (do withoutRecover tac; return none) fun e => do
    if e.isMaxHeartbeat then throw e
    s.restore
    return some e

/-- `vreact_try tac`: `try tac`, also when `tac` raises `maximum recursion depth` (see
`tryTactic`; the heartbeat limit is not caught). -/
elab "vreact_try " tac:tacticSeq : tactic => do
  let _ ← tryTactic (Lean.Elab.Tactic.evalTactic tac)

/-- Normalise hypotheses and goal with the model's simp set. -/
macro "vreact_norm" : tactic => `(tactic|
  (vreact_try simp (config := { zetaDelta := true, failIfUnchanged := false }) only [vreact_simp] at *))

theorem exists_prop_fst {b : Prop} {p : b → Prop} (h : ∃ x, p x) : b := h.elim fun x _ => x
theorem exists_prop_snd {b : Prop} {p : b → Prop} (h : ∃ x, p x) : p (exists_prop_fst h) :=
  h.elim fun _ hx => hx

open Lean Meta Elab Tactic in
/-- `vreact_unpack`: add the parts of hypotheses `a ∧ b` and `∃ (h : a), b h` (a proposition
`a`) as hypotheses, recursively.  A guarded contract `xs.length === 3 && forall(0, 3, i =>
xs[i] >= 0)` is `∃ (h : xs.length = 3), ∀ i …` (the index proofs of the second conjunct use
the first), which `omega` and `simp_all` cannot look into.  Copies are added; the original
hypotheses (which other terms may depend on) stay. -/
elab "vreact_unpack" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut work : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    work := work.push (mkFVar d.fvarId, ← instantiateMVars d.type)
  let mut n := 0
  repeat
    let some (pf, ty) := work.back? | break
    work := work.pop
    let ty ← whnfR ty
    let mut parts : List (Expr × Expr) := []
    if ty.isAppOfArity ``And 2 then
      parts := [(← mkAppM ``And.left #[pf], ty.appFn!.appArg!), (← mkAppM ``And.right #[pf], ty.appArg!)]
    else if ty.isAppOfArity ``Exists 2 then
      if ← isProp ty.appFn!.appArg! then
        let fst ← mkAppM ``exists_prop_fst #[pf]
        let snd ← mkAppM ``exists_prop_snd #[pf]
        parts := [(fst, ty.appFn!.appArg!), (snd, (← instantiateMVars (← inferType snd)).headBeta)]
    for (p, t) in parts do
      if n ≥ 64 then break
      n := n + 1
      let (_, g') ← (← g.assert (← mkFreshUserName `hpart) t p).intro1P
      g := g'
      work := work.push (p, t)
  replaceMainGoal [g]

section KeyFacts
open Lean Meta Elab Tactic

/-- A key comparison `JS.eq e k` / `JS.eq k e` in the body of a predicate over `x` (`e`
mentions `x`, `k` does not): `(fun x => e, k, inst, k first?)`. -/
private def keyCmp? (x c : Expr) : MetaM (Option (Expr × Expr × Expr × Bool)) := do
  unless c.isAppOfArity ``JS.eq 4 do return none
  let a := c.getArg! 2; let b := c.getArg! 3
  let inA := a.containsFVar x.fvarId!; let inB := b.containsFVar x.fvarId!
  if inA && !inB then return some (← mkLambdaFVars #[x] a, b, c.getArg! 1, false)
  if inB && !inA then return some (← mkLambdaFVars #[x] b, a, c.getArg! 1, true)
  return none

/-- A key test `ite (e = k) A B` / `ite (k = e) A B` inside `b` (`e` mentions `x`, `k` does
not), as `(the ite, e, k, k first?)`. -/
private def keyIte? (x b : Expr) : Option (Expr × Expr × Expr × Bool) := Id.run do
  let some t := b.find? fun s => Id.run do
      unless s.isAppOfArity ``ite 5 do return false
      let c := s.getArg! 1
      unless c.isAppOfArity ``Eq 3 do return false
      let l := c.getArg! 1; let r := c.getArg! 2
      let inL := l.containsFVar x.fvarId!; let inR := r.containsFVar x.fvarId!
      return (inL && !inR) || (inR && !inL)
    | return none
  let c := t.getArg! 1
  let l := c.getArg! 1; let r := c.getArg! 2
  if l.containsFVar x.fvarId! then return some (t, l, r, false) else return some (t, r, l, true)

/-- The facts of `Lists.lean` ("counts by key") for the count `(l.filter p).length`. -/
private def keyFactsOf (p l : Expr) : MetaM (Array Expr) := do
  let .lam n ty body bi := p | return #[]
  withLocalDecl n bi ty fun x => do
    let b := body.instantiate1 x
    let mut out := #[]
    -- deleting / keeping by key: `fun y => !JS.eq y.id k`, `fun y => JS.eq y.id k`
    let (neg, c) := if b.isAppOfArity ``Bool.not 1 || b.isAppOfArity ``not 1 then (true, b.appArg!) else (false, b)
    if let some (f, k, inst, kFirst) ← keyCmp? x c then
      let lem := match neg, kFirst with
        | true, false => ``length_filter_ne_key | true, true => ``length_filter_ne_key'
        | false, false => ``length_filter_eq_key | false, true => ``length_filter_eq_key'
      out := out.push (← mkAppOptM lem #[none, none, some inst, some f, some k, some l])
    -- a predicate after a map-update by key: `fun y => … (if y.id = k then A else B) …`
    if let some (t, e, k, kFirst) := keyIte? x b then
      let f ← mkLambdaFVars #[x] e
      let β ← inferType k
      let inst ← synthInstance (← mkAppM ``DecidableEq #[β])
      -- `q`: the predicate with the `else` branch (the elements whose key is not `k`)
      let q ← mkLambdaFVars #[x] (b.replace fun s => if s == t then some (t.getArg! 4) else none)
      let extra ← withLocalDeclD `z (← inferType t) fun zv => do
        let bAbs := b.replace fun s => if s == t then some zv else none
        -- h : ∀ x, f x ≠ k → p x = q x  (`congrArg` of `if_neg` at the `ite`)
        let h ← withLocalDeclD `hx (← mkAppM ``Ne #[e, k]) fun hx => do
          let hnc ← if kFirst then
              withLocalDeclD `he (t.getArg! 1) fun he => do mkLambdaFVars #[he] (mkApp hx (← mkEqSymm he))
            else pure hx
          let eqIte ← mkAppOptM ``if_neg #[t.getArg! 1, t.getArg! 2, hnc, t.getArg! 0, t.getArg! 3, t.getArg! 4]
          let pf ← mkCongrArg (← mkLambdaFVars #[zv] bAbs) eqIte
          mkLambdaFVars #[x, hx] pf
        let hsymm ← withLocalDeclD `hx (← mkAppM ``Ne #[e, k]) fun hx => do
          mkLambdaFVars #[x, hx] (← mkEqSymm (mkApp2 h x hx))
        let le ← mkAppOptM ``length_filter_le_of_agree_off_key #[none, none, some inst, some p, some q, some f, some k, some l, some h]
        let ge ← mkAppOptM ``length_filter_le_of_agree_off_key #[none, none, some inst, some q, some p, some f, some k, some l, some hsymm]
        let eq ← mkAppOptM ``length_filter_agree_off_key #[none, none, some inst, some p, some q, some f, some k, some l, some h]
        return #[le, ge, eq]
      out := out ++ extra
    return out

/-- `vreact_keyfacts`: for each count `(l.filter P).length` in the goal or a hypothesis whose
predicate deletes/keeps by a key or was map-updated by a key, add the facts of `Lists.lean`
("counts by key"), instantiated and beta-reduced, as hypotheses.  (`grind` cannot match
patterns inside the predicate.) -/
elab "vreact_keyfacts" : tactic => withMainContext do
  let goal ← getMainGoal
  let lctx ← getLCtx
  let mut targets : Array Expr := #[← instantiateMVars (← goal.getType)]
  for d in lctx do
    if !d.isImplementationDetail then targets := targets.push (← instantiateMVars d.type)
  let found ← IO.mkRef (#[] : Array (Expr × Expr))
  for t in targets do
    forEachExpr t fun sub => do
      if sub.hasLooseBVars || sub.hasMVar then return
      if sub.hasAnyFVar (fun fv => !lctx.contains fv) then return
      let_expr List.length _ fl := sub | return
      let_expr List.filter _ p l := fl | return
      unless p.isLambda do return
      let cur ← found.get
      unless cur.any (· == (p, l)) do found.set (cur.push (p, l))
  if (← found.get).isEmpty then return
  let mut have_ : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail then have_ := have_.push (← instantiateMVars d.type)
  let mut g := goal
  for (p, l) in ← found.get do
    let facts ← try keyFactsOf p l catch _ => pure #[]
    for pf in facts do
      let ty ← try Core.betaReduce (← instantiateMVars (← inferType pf)) catch _ => continue
      if have_.contains ty then continue
      have_ := have_.push ty
      let (_, g') ← (← g.assert (← mkFreshUserName `hkey) ty pf).intro1P
      g := g'
  replaceMainGoal [g]

end KeyFacts

section Bounded
open Lean Meta Elab Tactic

/-- The parts of a hypothesis `pf : ty` along `∧` and guarded `∃ (h : a), b h`. -/
private partial def hypParts (pf ty : Expr) (fuel : Nat := 6) : MetaM (Array (Expr × Expr)) := do
  let ty ← whnfR ty
  if fuel == 0 then return #[(pf, ty)]
  if ty.isAppOfArity ``And 2 then
    return (← hypParts (← mkAppM ``And.left #[pf]) ty.appFn!.appArg! (fuel - 1)) ++
      (← hypParts (← mkAppM ``And.right #[pf]) ty.appArg! (fuel - 1))
  if ty.isAppOfArity ``Exists 2 then
    if ← isProp ty.appFn!.appArg! then
      let fst ← mkAppM ``exists_prop_fst #[pf]
      let snd ← mkAppM ``exists_prop_snd #[pf]
      return #[(fst, ty.appFn!.appArg!)] ++
        (← hypParts snd ((← instantiateMVars (← inferType snd)).headBeta) (fuel - 1))
  return #[(pf, ty)]

/-- A bounded quantifier `∀ i : Int, (h : a i) → …` (`forall(lo, hi, i => …)`). -/
private def isBoundedForall (ty : Expr) : MetaM Bool := do
  let .forallE n d b bi := ty | return false
  unless d.isConstOf ``Int do return false
  withLocalDecl n bi d fun x => do
    let .forallE _ a _ _ := b.instantiate1 x | return false
    isProp a

/-- The `Int` index terms of the goal and hypotheses: `c` of `xs[c.toNat]` and of `JS.get xs c _`,
and `k` of `xs[k]` for a numeral `k`. -/
private def indexTerms (targets : Array Expr) (lctx : LocalContext) : MetaM (Array Expr) := do
  let found ← IO.mkRef (#[] : Array Expr)
  let add (c : Expr) : MetaM Unit := do
    let cur ← found.get
    if cur.size < 12 && !cur.contains c then found.set (cur.push c)
  for t in targets do
    forEachExpr t fun e => do
      if e.hasLooseBVars || e.hasMVar then return
      if e.hasAnyFVar (fun fv => !lctx.contains fv) then return
      if e.isAppOfArity ``GetElem.getElem 8 then
        let n := e.getArg! 6
        if n.isAppOfArity ``Int.toNat 1 then add n.appArg!
        else if let some k := n.nat? then add (toExpr (k : Int))
        else if let .lit (.natVal k) := n then add (toExpr (k : Int))
      else if e.isAppOfArity ``JS.get 4 then add (e.getArg! 2)
  return (← found.get)

/-- `∀ xs, B` with the proofs in `B` that use its propositional binders made binders of their own,
so the propositional binders become plain implications: `∀ i (h₁ : 0 ≤ i) (h₂ : i < 3), P
(xs[i.toNat]'(… h₂ …))` ↦ `∀ i, 0 ≤ i → i < 3 → ∀ (hp : i.toNat < xs.length), P (xs[i.toNat]'hp)`
(equivalent by proof irrelevance), with the proof of the new statement from `pf`. -/
private def genProofs (pf ty : Expr) : MetaM (Option (Expr × Expr)) :=
  forallTelescope ty fun xs body => do
    let propXs ← xs.filterM fun x => do isProp (← inferType x)
    if propXs.isEmpty then return none
    let isPropX (fv : FVarId) : Bool := propXs.any (·.fvarId! == fv)
    unless body.hasAnyFVar isPropX do return none
    let lctx ← getLCtx
    let found ← IO.mkRef (#[] : Array Expr)
    discard <| Meta.transform body (pre := fun e => do
      if e.hasLooseBVars then return .continue
      if !e.hasAnyFVar isPropX then return .done e
      if e.isFVar then return .done e
      -- binders inside `body` (visited as temporary fvars) must not occur in the proof
      if e.hasAnyFVar (fun fv => !lctx.contains fv) then return .continue
      if ← isProof e then
        let ety ← instantiateMVars (← inferType e)
        if !ety.hasAnyFVar isPropX then
          found.modify fun a => if a.contains e then a else a.push e
          return .done e
      return .continue)
    let ps ← found.get
    if ps.isEmpty then return none
    let tys ← ps.mapM fun p => do instantiateMVars (← inferType p)
    withLocalDeclsDND (tys.mapIdx fun i t => (Name.mkSimple s!"hp{i}", t)) fun hps => do
      let body' := body.replace fun s => (ps.idxOf? s).map (hps[·]!)
      if body'.hasAnyFVar isPropX then return none
      let ty' ← mkForallFVars (xs ++ hps) body'
      let pf' ← mkLambdaFVars (xs ++ hps) (mkAppN pf xs)
      -- by proof irrelevance
      unless ← isDefEq (← inferType pf') ty' do return none
      return some (pf', ty')

/-- A proof in `tgt` that uses `fv`, with a statement of it that does not: a maximal proof whose
type does not mention `fv`, or the bound proof of an index `l[n]'q` whose `l` and `n` do not
(its statement `n < l.length` then does not either, although the type `q` was elaborated with
may: `xs[0]'(… : 0 < (f xs h).length)` for an unfolded `f xs h`). -/
private def proofUsing? (tgt : Expr) (fv : FVarId) : MetaM (Option (Expr × Expr)) := do
  let lctx ← getLCtx
  let found ← IO.mkRef (none : Option (Expr × Expr))
  discard <| Meta.transform tgt (pre := fun e => do
    if (← found.get).isSome || !e.containsFVar fv then return .done e
    if e.hasLooseBVars || e.isFVar then return .continue
    if e.hasAnyFVar (fun f => !lctx.contains f) then return .continue
    if e.isAppOfArity ``GetElem.getElem 8 then
      let q := e.getArg! 7
      if q.containsFVar fv && !(e.getArg! 5).containsFVar fv && !(e.getArg! 6).containsFVar fv then
        found.set (some (q, (mkApp2 (e.getArg! 3) (e.getArg! 5) (e.getArg! 6)).headBeta))
        return .done e
    if ← isProof e then
      let ety ← instantiateMVars (← inferType e)
      if !ety.containsFVar fv then
        found.set (some (e, ety))
        return .done e
    return .continue)
  found.get

/-- The goal without its dependency on the hypothesis `fv`: the proofs in the goal that use it are
generalised one by one (`∀ (hp : P), G hp` implies `G p` by proof irrelevance), then `fv` is
cleared.  `none` if another local depends on it, or `fv` occurs outside such a proof. -/
private def dropDependency (g : MVarId) (fv : FVarId) : MetaM (Option MVarId) := do
  if (← g.withContext getLCtx).any (fun d => d.fvarId != fv &&
      (d.type.containsFVar fv || (d.value?.map (·.containsFVar fv)).getD false)) then return none
  let mut g := g
  for _ in [0:32] do
    let tgt ← instantiateMVars (← g.getType)
    unless tgt.containsFVar fv do return some (← g.clear fv)
    let some (p, pty) ← g.withContext (proofUsing? tgt fv) | return none
    g ← g.withContext do
      let abs ← kabstract tgt p
      unless abs.hasLooseBVars do throwError "vreact: no occurrence"
      let g' ← mkFreshExprSyntheticOpaqueMVar (.forallE `hp pty abs .default) (← g.getTag)
      g.assign (mkApp g' p)
      let (_, g'') ← g'.mvarId!.intro1P
      return g''
  return none

/-- A guarded existential `∃ (h : a), b h` (a proposition `a`) whose body uses the guard: the
translation of `a && b` where `b` indexes with a bound from `a` (`xs.length > 0 && xs[0] >= 1`). -/
private partial def hasDepGuard (ty : Expr) (fuel : Nat := 8) : MetaM Bool := do
  if fuel == 0 then return false
  let ty ← whnfR ty
  if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Or 2 then
    return (← hasDepGuard ty.appFn!.appArg! (fuel - 1)) || (← hasDepGuard ty.appArg! (fuel - 1))
  if ty.isAppOfArity ``Exists 2 then
    let .lam n d b bi := ty.appArg! | return false
    if b.hasLooseBVar 0 && (← isProp d) then return true
    return ← withLocalDecl n bi d fun x => hasDepGuard (b.instantiate1 x) (fuel - 1)
  if let .forallE n d b bi := ty then
    return ← withLocalDecl n bi d fun x => hasDepGuard (b.instantiate1 x) (fuel - 1)
  return false

/-- `ty` (the statement of a part of the hypothesis `fv`) without `fv`: each proof in it that uses
`fv` (`proofUsing?`, e.g. the index proof `exists_prop_fst fv` of the second part of `∃ (h :
xs.length > 0), xs[0]'h ≥ 1`) becomes a hypothesis of its own, asserted with that proof. -/
private def abstractProofsUsing (g : MVarId) (fv : FVarId) (ty : Expr) : MetaM (Option (MVarId × Expr)) := do
  let mut g := g
  let mut ty := ty
  for _ in [0:32] do
    unless ty.containsFVar fv do return some (g, ty)
    let some (p, pty) ← g.withContext (proofUsing? ty fv) | return none
    let abs ← g.withContext (kabstract ty p)
    unless abs.hasLooseBVars do return none
    let (h, g') ← (← g.assert (← mkFreshUserName `hidx) pty p).intro1P
    g := g'
    ty := abs.instantiate1 (mkFVar h)
  return none

/-- `vreact_bounded`: bounded quantifiers among the hypotheses (`forall(lo, hi, i => P)` is
`∀ i : Int, lo ≤ i → i < hi → P i`, possibly inside guards `∃ (h : a), …` and `∧`).
1. A hypothesis that has one, or a guarded existential whose body indexes with its guard
   (`hasDepGuard`), is replaced by its parts: the guards, the other conjuncts with the proofs that
   use the hypothesis made hypotheses of their own (`abstractProofsUsing`), and the quantifiers
   with their index proofs made non-dependent (`genProofs`).  `grind`'s arithmetic normaliser raises `maximum
   recursion depth` on a binder with a numeral bound that a later proof depends on, `∀ i (h : i <
   3), … xs[i.toNat]'(… h …) …` (a core Lean 4.35 limitation), and it does so on any hypothesis of
   the context.  A hypothesis only the goal depends on (`vreact_expose` made a normalised copy of
   it, which is replaced) is removed after the proofs in the goal that use it are generalised
   (`dropDependency`).
2. The quantifiers are instantiated at the index terms of the goal, for each whose bounds `omega`
   proves: `grind` instantiates them by E-matching on `xs[i.toNat]`, which `xs[0]` (a numeral
   index, after `Int.toNat 0` is evaluated) does not match. -/
elab "vreact_bounded" : tactic => withMainContext do
  let goal ← getMainGoal
  let lctx ← getLCtx
  let tgt ← instantiateMVars (← goal.getType)
  let mut have_ : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail then have_ := have_.push (← instantiateMVars d.type)
  let mut g := goal
  let mut parts : Array (Expr × Expr) := #[]
  let mut toClear : Array FVarId := #[]
  let mut toDrop : Array FVarId := #[]
  for d in lctx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    -- cheap filter: some binder over `Int` with a guard, or a guarded existential
    let bounded := ty.find? (fun s => match s with
        | .forallE _ (.const ``Int _) (.forallE ..) _ => true | _ => false) |>.isSome
    let guarded ← hasDepGuard ty
    unless bounded || guarded do continue
    -- depended on (by the goal or another local): `vreact_expose` added a normalised copy
    let used := tgt.containsFVar d.fvarId || lctx.any fun d' =>
      d'.index > d.index && (d'.type.containsFVar d.fvarId || (d'.value?.map (·.containsFVar d.fvarId)).getD false)
    if used then
      toDrop := toDrop.push d.fvarId
      continue
    let leaves ← hypParts (mkFVar d.fvarId) ty
    -- a plain bounded quantifier: instantiated as it is
    if leaves.size == 1 && !guarded then
      if let some (pf', pty') ← g.withContext (genProofs (mkFVar d.fvarId) ty) then
        let (fv, g') ← (← g.assert (← mkFreshUserName `hpart) pty' pf').intro1P
        g := g'
        parts := parts.push (mkFVar fv, pty')
        toClear := toClear.push d.fvarId
      else if ← isBoundedForall ty then parts := parts.push (mkFVar d.fvarId, ty)
      continue
    -- the parts become hypotheses (the quantifiers are instantiated through these)
    let saved ← saveState
    let g0 := g
    let parts0 := parts
    let have0 := have_
    let mut ok := true
    for (pf, pty) in leaves do
      let some (g', pty') ← abstractProofsUsing g d.fvarId pty | ok := false; break
      g := g'
      let (pf, pty) ← if ← isBoundedForall pty' then
          pure ((← g.withContext (genProofs pf pty')).getD (pf, pty'))
        else pure (pf, pty')
      -- a duplicate of another hypothesis (not of `d` itself, which is cleared)
      if !(← isBoundedForall pty) && (have_.size > have0.size && (have_.extract have0.size have_.size).contains pty
          || lctx.any fun d' => d'.fvarId != d.fvarId && !d'.isImplementationDetail && d'.type == pty) then continue
      have_ := have_.push pty
      let (fv, g') ← (← g.assert (← mkFreshUserName `hpart) pty pf).intro1P
      g := g'
      if ← isBoundedForall pty then parts := parts.push (mkFVar fv, pty)
    if ok then toClear := toClear.push d.fvarId
    else
      saved.restore
      g := g0
      parts := parts0
      have_ := have0
  g ← g.tryClearMany toClear
  if !parts.isEmpty || !toClear.isEmpty then
    for fv in toDrop do
      let saved ← saveState
      if let some g' ← (try dropDependency g fv catch _ => pure none) then g := g'
      else saved.restore
  if parts.isEmpty then replaceMainGoal [g]; return
  let mut targets : Array Expr := #[tgt]
  for d in lctx do
    if !d.isImplementationDetail then targets := targets.push (← instantiateMVars d.type)
  let cands ← indexTerms targets lctx
  for (pf, _) in parts.toList.take 8 do
    for c in cands do
      let some fact ← g.withContext (do
          let mut e := mkApp pf c
          let mut ty ← whnfR (← instantiateMVars (← inferType e))
          -- discharge the guards with `omega`
          repeat
            let .forallE _ a _ _ := ty | break
            unless ← isProp a do break
            let m ← mkFreshExprMVar a
            let saved ← getGoals
            let ok ← (do setGoals [m.mvarId!]; evalTactic (← `(tactic| omega)); pure true) <|> pure false
            setGoals saved
            unless ok do return none
            e := mkApp e (← instantiateMVars m)
            ty ← whnfR (← instantiateMVars (← inferType e))
          return some (e, ty) : TacticM (Option (Expr × Expr)))
        | continue
      let (e, ty) := fact
      if have_.contains ty then continue
      have_ := have_.push ty
      let (_, g') ← (← g.assert (← mkFreshUserName `hinst) ty e).intro1P
      g := g'
  replaceMainGoal [g]

end Bounded

open Lean Meta Elab Tactic in
/-- Run `tac` on the main goal as one alternative of `vreact_finish`: `none` if it closes the
goal, otherwise (state restored) the exception.  Under `tryTactic`, so an alternative that
raises `maximum recursion depth` falls through to the next. -/
private def attemptClose (tac : TSyntax `tactic) : TacticM (Option Exception) := tryTactic do
  evalTactic tac
  unless (← getUnsolvedGoals).isEmpty do throwError "unsolved goals"

open Lean Meta Elab Tactic in
/-- The cheap alternatives (`done`, `grind`, `omega`) on the main goal.  `none` if one closes
it, otherwise the error to report: `grind`'s (it shows the hypotheses and the case it got
stuck in) — never a later alternative's message such as `simp_all made no progress`. -/
private def finishCheap : TacticM (Option Exception) := withMainContext do
  let goal ← getMainGoal
  if (← attemptClose (← `(tactic| done))).isNone then return none
  let grindErr ← attemptClose (← `(tactic| grind))
  if grindErr.isNone then return none
  if (← attemptClose (← `(tactic| omega))).isNone then return none
  match grindErr with
  | some e =>
    -- a runtime exception is reported as an ordinary error (the caller may still try
    -- the other conjuncts, and `try … catch` does not catch runtime exceptions).
    -- Not Lean's own wording: the report would read that as an aborted declaration.
    if e.isRuntime then
      return some (.error (← getRef) m!"vreact_auto could not prove the goal (grind stopped at Lean's recursion limit){indentD (MessageData.ofGoal goal)}")
    return some e
  | none => return some (.error (← getRef) m!"vreact_auto could not prove the goal{indentD (MessageData.ofGoal goal)}")

open Lean Meta Elab Tactic in
/-- The expensive fallbacks (`simp_all` variants) after `finishCheap` failed with `err`:
`none` if one closes the goal, otherwise `err`. -/
private def finishSlow (err : Exception) : TacticM (Option Exception) := withMainContext do
  if (← attemptClose (← `(tactic| (simp_all; done)))).isNone then return none
  if (← attemptClose (← `(tactic| (simp_all; grind)))).isNone then return none
  -- guarded contracts (`∃ (h : a), b h`): arithmetic and simp facts inside them
  if (← attemptClose (← `(tactic| (vreact_unpack; omega)))).isNone then return none
  if (← attemptClose (← `(tactic| (vreact_unpack; simp_all; done)))).isNone then return none
  return some err

open Lean Meta in
/-- The conjuncts of `g`'s target (split along `∧` at all levels), as goals. -/
private partial def conjunctGoals (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  if tgt.isAppOfArity ``And 2 then
    let [g1, g2] ← g.apply (mkConst ``And.intro) | return [g]
    return (← conjunctGoals g1) ++ (← conjunctGoals g2)
  return [g]

open Lean Meta Elab Tactic in
/-- `vreact_finish`: close a normalised goal by `grind` (or `omega`); when that fails on a
conjunction, prove the conjuncts one by one (smaller goals, and the report names only the
conjuncts that fail).  The expensive `simp_all` fallbacks run on the whole goal only if it has
at most two conjuncts or no hypotheses (there they cost about as much as on one conjunct, and
they often close e.g. `Robust inv o ∧ o.emit = none` or a ground `init_inv` at once); a
larger conjunction goes straight to its
conjuncts, all at once: running the fallbacks, or `grind`, at every level of a large
invariant (`wf(b) ∧ …` of a reducer with many arms) cost most of the obligation's budget,
since the hypotheses dominate the cost of each call and the intermediate conjunctions mostly
fail like the whole.  A conjunction the fallbacks prove has conjuncts they prove. -/
private def finishCore : TacticM (Option Exception) := do
  let some err ← finishCheap | return none
  let g ← getMainGoal
  let s ← saveState
  let n := (← conjunctGoals g).length
  s.restore
  -- without hypotheses (e.g. `init_inv`: only `hpre : True`) `simp_all` is `simp` on the goal:
  -- on the whole no dearer than on the parts
  let noHyps ← g.withContext do
    (← getLCtx).allM fun d => do
      if d.isImplementationDetail || !(← isProp d.type) then return true
      return (← whnfR (← instantiateMVars d.type)).isConstOf ``True
  if n ≤ 2 || noHyps then
    let some err ← finishSlow err | return none
    if n ≤ 1 then return some err
  let mut firstErr : Option Exception := none
  for gi in ← conjunctGoals g do
    setGoals [gi]
    let some e ← finishCheap | continue
    let some e ← finishSlow e | continue
    if firstErr.isNone then firstErr := some e
  setGoals []
  return firstErr

open Lean Meta in
/-- Terms of the goal (then of the hypotheses) whose type is a small enumeration or union (a
non-recursive inductive type without parameters or indices, with 2–8 constructors, other than
`Bool`/`Int`): locals, and fields of locals (`σ.mode`), in order of occurrence.  (After `split`
on a `match t with … | _ => …` the goal may be `False` with facts `t = .c v q → False`.) -/
private def splitCandidates (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let lctx ← getLCtx
  let mut targets := #[← instantiateMVars (← g.getType)]
  for d in lctx do
    if !d.isImplementationDetail && !d.isLet then targets := targets.push (← instantiateMVars d.type)
  let found ← IO.mkRef (#[] : Array Expr)
  for tgt in targets do
   forEachExpr tgt fun e => do
     if e.hasLooseBVars || e.hasMVar then return
     -- binders visited by `forEachExpr` become temporary fvars
     if e.hasAnyFVar (fun fv => !lctx.contains fv) then return
     let ok ← match e with
       | .fvar fv => pure !(lctx.get! fv).isLet
       | _ =>
         if let .const fn _ := e.getAppFn then
           pure ((← getProjectionFnInfo? fn).isSome && e.getAppNumArgs ≥ 1 && e.appArg!.isFVar)
         else pure false
     unless ok do return
     let ty ← whnfR (← inferType e)
     let .const n _ := ty | return
     if n == ``Int || n == ``Bool || n == ``Nat then return
     let some (.inductInfo ii) := (← getEnv).find? n | return
     if ii.isRec || ii.numParams > 0 || ii.numIndices > 0 || ii.ctors.length < 2 || ii.ctors.length > 8 then
       return
     let cur ← found.get
     unless cur.contains e do found.set (cur.push e)
  return (← found.get)

open Lean Meta in
/-- Case split on `e` (a local, or a field of one: generalised with an equation first). -/
private def casesOn (g : MVarId) (e : Expr) : MetaM (Array MVarId) := g.withContext do
  let (fv, g) ← match e with
    | .fvar fv => pure (fv, g)
    | _ => do
      let (fvs, g) ← g.generalize #[{ expr := e, xName? := `x, hName? := `hx }]
      pure (fvs[0]!, g)
  return (← g.cases fv).map (·.mvarId)

open Lean Meta in
/-- A guarded existential goal `∃ (h : a), b h` (a guarded contract `xs.length === 3 && forall(0,
3, i => xs[i] >= 0)` to establish): the goals `a`, then `b ?h`. -/
private def splitExistsProp? (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  unless tgt.isAppOfArity ``Exists 2 do return none
  unless ← isProp tgt.appFn!.appArg! do return none
  some <$> g.apply (← mkConstWithFreshMVarLevels ``Exists.intro) { newGoals := .all }

open Lean Meta Elab Tactic in
/-- A goal `∀ i : Int, lo ≤ i → i < hi → …` with numeral bounds (`forall(0, 3, i => …)` to
establish, at most 8 values): introduced, and split into the cases `i = lo`, …, `i = hi - 1`
(substituted, so `[a, b, c][i.toNat]` evaluates). -/
private def enumBounded? (g : MVarId) : TacticM (Option (List MVarId)) := do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ (.const ``Int _) _ _ := tgt | return none
  let (_, g) ← g.intros
  g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      unless (← instantiateMVars d.type).isConstOf ``Int do continue
      let i := mkFVar d.fvarId
      let mut lo? : Option Int := none
      let mut hi? : Option Int := none
      for h in ← getLCtx do
        let t ← instantiateMVars h.type
        if t.isAppOfArity ``LE.le 4 && t.appArg! == i then
          if let some v ← getIntValue? (t.getArg! 2) then lo? := some v
        if t.isAppOfArity ``LT.lt 4 && t.getArg! 2 == i then
          if let some v ← getIntValue? t.appArg! then hi? := some v
      let (some lo, some hi) := (lo?, hi?) | continue
      unless lo < hi && hi - lo ≤ 8 do continue
      let mut out := []
      let mut cur := g
      for k in List.range (hi - lo).toNat do
        let (pos, neg) ← cur.byCases (← mkEq i (toExpr (lo + k)))
        out := out ++ [← Lean.Meta.subst pos.mvarId pos.fvarId]
        cur := neg.mvarId
      -- the remaining case contradicts the bounds
      setGoals [cur]
      evalTactic (← `(tactic| omega))
      return some out
    return none

open Lean Meta Elab Tactic in
/-- `vreact_finish` (see `finishCore`), with fallbacks for the goals it fails on, each case
normalised again and finished at most `depth` levels deep:
* a guarded existential goal `∃ (h : a), b h`: `a`, then `b h` (`splitExistsProp?`);
* a bounded quantifier with numeral bounds: one case per value (`enumBounded?`);
* a goal that mentions a small enumeration or union (`c : Color`, `t : T` of a discriminated
  union, `σ.mode`): one case per constructor (the `match`es and `===` tests on it reduce).
  `grind` does not split such a variable itself, so a true three-way disjunctive postcondition
  `(c === "red" && n === 1) || …` failed.
Only fallbacks: a goal proved without them costs nothing more, and a failure reports the error
on the original goal. -/
partial def vreactFinishAux (depth : Nat) : TacticM Unit := do
  let s ← saveState
  let some err ← finishCore | return
  if depth == 0 then throw err
  s.restore
  let g ← getMainGoal
  let finishAll (goals : List MVarId) : TacticM Unit := do
    for gi in goals do
      if ← gi.isAssigned then continue
      setGoals [gi]
      evalTactic (← `(tactic| vreact_norm))
      evalTactic (← `(tactic| vreact_try (repeat' split)))
      evalTactic (← `(tactic| all_goals vreact_norm))
      evalTactic (← `(tactic| all_goals vreact_keyfacts))
      evalTactic (← `(tactic| all_goals vreact_bounded))
      for gj in ← getGoals do
        setGoals [gj]
        vreactFinishAux (depth - 1)
    setGoals []
  -- guarded existentials, bounded quantifiers
  if (← tryTactic do
      let some goals ← splitExistsProp? g | throwError "no"
      finishAll goals).isNone then return
  s.restore
  if (← tryTactic do
      let some goals ← enumBounded? g | throwError "no"
      finishAll goals).isNone then return
  s.restore
  -- enumerations and unions
  let cands ← splitCandidates g
  let some e := cands[0]? | throw err
  let r ← tryTactic do finishAll (← casesOn g e).toList
  if r.isSome then
    s.restore
    throw err

open Lean Elab Tactic in
def vreactFinish : TacticM Unit := vreactFinishAux 3

elab "vreact_finish" : tactic => vreactFinish

syntax "vreact_auto" : tactic
macro_rules
  | `(tactic| vreact_auto) => `(tactic|
      (intros
       vreact_expose
       vreact_contracts
       vreact_try (repeat' split)
       all_goals vreact_norm
       all_goals vreact_contracts
       all_goals vreact_norm
       all_goals (
         vreact_try (repeat' split)
         all_goals vreact_norm
         -- calls exposed by the last split (e.g. in match arms of a transparent reducer)
         all_goals vreact_contracts
         all_goals vreact_norm
         all_goals vreact_keyfacts
         all_goals vreact_bounded
         all_goals vreact_finish)))

end VReact
