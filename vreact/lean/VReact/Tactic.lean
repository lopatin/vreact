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
2. split `if`/`match` in the goal, normalise again (a goal with a membership in a map-update
   also with the lemmas of `Lists.lean` that state it about the updated elements,
   `vreact_memmap`); instantiate the contracts of the calls in the goal and its hypotheses
   (`vreact_contracts`), after opening the binders that a call is under (`vreact_open`: the state
   of a robust update, the element of a `map`/`every`); add the facts `grind` cannot find by
   E-matching: counts of filters by key
   (`vreact_keyfacts`), the parts and instances of bounded quantifiers and guarded existentials,
   with a goal's own guarded binders made plain implications (`vreact_bounded`), distinct keys
   and counts through chains of list operations, maps that keep the key included
   (`vreact_subperm`);
3. close each case with `grind` (congruence closure + E-matching + linear
   integer arithmetic + case splitting) or `omega`; if both fail on a
   conjunction, prove the conjuncts separately; on a goal that is not a
   conjunction, fall back to `simp_all` variants (also on the parts of guarded
   contracts `∃ (h : a), b h`, `vreact_unpack`); a failure reports `grind`'s
   goal (`vreact_finish`); if all of that fails, split a conjunction into its conjuncts, a
   guarded existential goal, a bounded quantifier with numeral bounds, or a small
   enumeration/union of the goal, and finish each case (`vreactFinishAux`).  Every alternative runs under `tryTactic`: a runtime
   exception such as `maximum recursion depth` (which `first`/`try` let
   through) makes it fail like any other error — except the heartbeat limit,
   `vreact_ob`'s per-obligation budget, which is passed on.

The normalisation set is the simp attribute `vreact_simp` (so a typo in a lemma
name is a build error of this library, never a silent weakening of the tactic).
Users extend the automation by tagging their lemmas `@[vreact_simp]` (rewrite
rules) or `@[grind]`/`grind_pattern` (E-matching facts). (Not with `macro_rules`
for `vreact_auto` or other syntax: user proof files may contain only lemmas, see
`ProofCheck.lean`.)
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
  JS.Num.divInt JS.Num.divNum
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
-- a guard whose proof the guarded part does not use (`cells[i] >= 0 && cells[i] <= 2`: the index
-- proofs of the second conjunct do not need the first) is a conjunction: `grind` proves an `∃ (h :
-- a), b` goal under a bounded quantifier poorly
attribute [vreact_simp] exists_prop

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

/-- `repeat' split`, each split followed by `simp only []` (iota: a `match` on a constructor
reduces, an impossible case `some p = none` closes).  A `match` of the goal can stay after `split`
when it occurs under a binder: `holds(r, j, o)` in a frame `[...m].every(([j, o]) => … holds(r, j, o))`
with `r` the result of `const o = m.get(k); if (o === undefined) return m; …` is
`match h : (match h' : m.get k with …).get j with …`, and `split` on the inner match left
`match h' : some p with …` in the goal, which the next `split` split again, forever (until the
obligation's budget ran out). -/
macro "vreact_splits" : tactic => `(tactic|
  (vreact_try (repeat' (split <;> vreact_try simp (config := { failIfUnchanged := false }) only [] at *))))

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

open Lean Meta Elab Tactic in
/-- `vreact_memmap`: a goal with a membership in a map-update (`∃ a, a ∈ l ∧ f a = x`, from
`x ∈ l.map f` with `f : α → α`, `List.mem_map`) is normalised with the lemmas of `Lists.lean`
("Membership in a map-update"), which state the facts about the updated elements `f a` instead:
`grind` instantiated that existential for every conjunct of a reducer's invariant (`wf(b)` over
`[...todo, ...doing, ...done]` after a map-update arm). Only such goals: the lemmas are keyed
on `∃`/`∀`. -/
elab "vreact_memmap" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isUpd (e : Expr) : Bool := Id.run do
    unless e.isAppOfArity ``Exists 2 do return false
    let .lam _ ty b _ := e.appArg! | return false
    unless b.isAppOfArity ``And 2 do return false
    let m := b.appFn!.appArg!; let q := b.appArg!
    unless m.isAppOfArity ``Membership.mem 5 && q.isAppOfArity ``Eq 3 do return false
    let lhs := q.getArg! 1
    return q.getArg! 0 == ty && !lhs.isBVar && lhs.hasLooseBVar 0
  unless (tgt.find? isUpd).isSome do return
  evalTactic (← `(tactic| vreact_try simp (config := { zetaDelta := true, failIfUnchanged := false }) only
    [vreact_simp, ex_mem_map_and, ex_mem_map_or_and, ex_or_mem_map_and, ex_or_mem_map_or_and,
      ex_or_or_mem_map_and, all_mem_map, all_mem_map_or, all_or_mem_map, all_or_mem_map_or, all_or_or_mem_map]))

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
not), also negated (`ite (¬ e = k) B A`: `t.id !== id ? t : {...}`), as `(the ite, e, k, k first?,
negated?)`. -/
private def keyIte? (x b : Expr) : Option (Expr × Expr × Expr × Bool × Bool) := Id.run do
  let keyEq? (c : Expr) : Option (Expr × Expr × Bool) := Id.run do
    unless c.isAppOfArity ``Eq 3 do return none
    let l := c.getArg! 1; let r := c.getArg! 2
    let inL := l.containsFVar x.fvarId!; let inR := r.containsFVar x.fvarId!
    if inL && !inR then return some (l, r, false)
    if inR && !inL then return some (r, l, true)
    return none
  let cond? (c : Expr) : Option (Expr × Expr × Bool × Bool) :=
    match keyEq? c with
    | some (e, k, kf) => some (e, k, kf, false)
    | none => if c.isAppOfArity ``Not 1 then (keyEq? c.appArg!).map fun (e, k, kf) => (e, k, kf, true) else none
  let some t := b.find? fun s => s.isAppOfArity ``ite 5 && (cond? (s.getArg! 1)).isSome | return none
  let some (e, k, kf, neg) := cond? (t.getArg! 1) | return none
  return some (t, e, k, kf, neg)

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
    if let some (t, e, k, kFirst, neg) := keyIte? x b then
      let f ← mkLambdaFVars #[x] e
      let β ← inferType k
      let inst ← synthInstance (← mkAppM ``DecidableEq #[β])
      -- `q`: the predicate with the branch of the elements whose key is not `k` (`else`, or
      -- `then` of a negated test)
      let off := if neg then t.getArg! 3 else t.getArg! 4
      let q ← mkLambdaFVars #[x] (b.replace fun s => if s == t then some off else none)
      let extra ← withLocalDeclD `z (← inferType t) fun zv => do
        let bAbs := b.replace fun s => if s == t then some zv else none
        -- h : ∀ x, f x ≠ k → p x = q x  (`congrArg` of `if_neg`/`if_pos` at the `ite`)
        let h ← withLocalDeclD `hx (← mkAppM ``Ne #[e, k]) fun hx => do
          -- `¬ (e = k)` resp. `¬ (k = e)`: the condition (negated test) or its negation
          let hnc ← if kFirst then
              withLocalDeclD `he (← mkEq k e) fun he => do mkLambdaFVars #[he] (mkApp hx (← mkEqSymm he))
            else pure hx
          let eqIte ← mkAppOptM (if neg then ``if_pos else ``if_neg)
            #[t.getArg! 1, t.getArg! 2, hnc, t.getArg! 0, t.getArg! 3, t.getArg! 4]
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
  -- the list and the index must be closed; the bound proof may be a bound variable (`∀ (hp : 0 <
  -- xs.length), xs[0]'hp …`, a goal after `genGoal`)
  let closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasMVar && !e.hasAnyFVar (fun fv => !lctx.contains fv)
  for t in targets do
    forEachExpr t fun e => do
      if e.isAppOfArity ``GetElem.getElem 8 then
        let n := e.getArg! 6
        unless closed n && closed (e.getArg! 5) do return
        if n.isAppOfArity ``Int.toNat 1 then add n.appArg!
        else if let some k := n.nat? then add (toExpr (k : Int))
        else if let .lit (.natVal k) := n then add (toExpr (k : Int))
      else if e.isAppOfArity ``JS.get 4 then
        if closed (e.getArg! 2) && closed (e.getArg! 1) then add (e.getArg! 2)
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
generalised one by one (`∀ (hp : P), G hp` implies `G p` by proof irrelevance); `fv` stays.  `none`
if another local depends on it, or `fv` occurs outside such a proof. -/
private def freeGoal (g : MVarId) (fv : FVarId) : MetaM (Option MVarId) := do
  if (← g.withContext getLCtx).any (fun d => d.fvarId != fv &&
      (d.type.containsFVar fv || (d.value?.map (·.containsFVar fv)).getD false)) then return none
  let mut g := g
  for _ in [0:32] do
    let tgt ← instantiateMVars (← g.getType)
    unless tgt.containsFVar fv do return some g
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

/-- The parts of the hypothesis `fv : ty` (a candidate of `vreact_bounded` that nothing depends on),
asserted: `(goal, the bounded quantifiers among them, the statements asserted, whether `fv` is to be
cleared)`, or `none` (nothing to do, or a part that cannot be stated without `fv`: the caller
restores the state).  `isDup t`: `t` is already a hypothesis that stays. -/
private def candParts (g : MVarId) (fv : FVarId) (ty : Expr) (guarded : Bool) (isDup : Expr → Bool) :
    MetaM (Option (MVarId × Array (Expr × Expr) × Array Expr × Bool)) := do
  let leaves ← hypParts (mkFVar fv) ty
  -- one part, the hypothesis itself (`∃ i, ∃ (h : …), xs[i] < 0`, `(∃ (h : …), …) ∨ …`, `∀ x ∈ l,
  -- ∃ (h : …), …`): nothing to split, the hypothesis stays
  if leaves.size == 1 && guarded && !(← isBoundedForall ty) then return none
  -- a plain bounded quantifier: instantiated as it is
  if leaves.size == 1 && !guarded then
    if let some (pf', pty') ← g.withContext (genProofs (mkFVar fv) ty) then
      let (fv', g') ← (← g.assert (← mkFreshUserName `hpart) pty' pf').intro1P
      return some (g', #[(mkFVar fv', pty')], #[pty'], true)
    else if ← isBoundedForall ty then return some (g, #[(mkFVar fv, ty)], #[], false)
    return none
  -- the parts become hypotheses (the quantifiers are instantiated through these)
  let mut g := g
  let mut parts := #[]
  let mut tys := #[]
  for (pf, pty) in leaves do
    let some (g', pty') ← abstractProofsUsing g fv pty | return none
    g := g'
    let (pf, pty) ← if ← isBoundedForall pty' then
        pure ((← g.withContext (genProofs pf pty')).getD (pf, pty'))
      else pure (pf, pty')
    let bnd ← isBoundedForall pty
    if !bnd && (isDup pty || tys.contains pty) then continue
    tys := tys.push pty
    let (fv', g') ← (← g.assert (← mkFreshUserName `hpart) pty pf).intro1P
    g := g'
    if bnd then parts := parts.push (mkFVar fv', pty)
  return some (g, parts, tys, true)

/-- The proof arguments of `e` (closed, mentioning a local, not under a binder of `e`), with the
statement their position asks for (the binding domain of the function at the actual arguments: `n <
l.length` for `l[n]'p`, in terms of the normalised `l`, where `p`'s own type may mention a term
`simp` has rewritten since, e.g. an unfolded call `f xs h_pre`). -/
private partial def proofArgs (lctx : LocalContext) (e : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  let closed (x : Expr) : Bool := !x.hasLooseBVars && !x.hasAnyFVar (fun fv => !lctx.contains fv)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut acc ← proofArgs lctx f acc
    let mut fty ← inferType f
    for a in args do
      fty ← whnf fty
      let .forallE _ dom body _ := fty | return acc
      if a.hasFVar && !a.isFVar && closed a && closed dom && (← isProp dom) then
        unless acc.any (·.1 == a) do acc := acc.push (a, dom)
      else
        acc ← proofArgs lctx a acc
      fty := body.instantiate1 a
    return acc
  | .lam n d b bi | .forallE n d b bi =>
    let acc ← proofArgs lctx d acc
    withLocalDecl n bi d fun x => proofArgs lctx (b.instantiate1 x) acc
  | .letE n t v b _ =>
    let acc ← proofArgs lctx v acc
    withLetDecl n t v fun x => proofArgs lctx (b.instantiate1 x) acc
  | .mdata _ x => proofArgs lctx x acc
  | .proj _ _ x => proofArgs lctx x acc
  | _ => return acc

/-- The proofs in the leaf `l` of a goal (`proofArgs`) made binders of their own: `(∀ hps, l[hps],
fun p' => p' ps)`, or `none`. -/
private def genLeaf (l : Expr) : MetaM (Option (Expr × Expr)) := do
  let found ← proofArgs (← getLCtx) l #[]
  if found.isEmpty then return none
  let ps := found.map (·.1)
  let tys := found.map (·.2)
  withLocalDeclsDND (tys.mapIdx fun i t => (Name.mkSimple s!"hp{i}", t)) fun hps => do
    let l' := l.replace fun s => (ps.idxOf? s).map (hps[·]!)
    let ty' ← mkForallFVars hps l'
    let back ← withLocalDeclD `p ty' fun p => do mkLambdaFVars #[p] (mkAppN p ps)
    return some (ty', back)

/-- A propositional binder on the spine (`∧`, `∃`, `∀`) of the goal `ty` that its body depends on:
`∀ i (h : 0 ≤ i), … xs[i]'(… h …)`, `∃ (h : a), … h …` (not inside proofs or leaves). -/
private partial def spineDep (ty : Expr) (fuel : Nat := 12) : MetaM Bool := do
  if fuel == 0 then return false
  let ty := ty.headBeta
  if ty.isAppOfArity ``And 2 then
    return (← spineDep ty.appFn!.appArg! (fuel - 1)) || (← spineDep ty.appArg! (fuel - 1))
  if ty.isAppOfArity ``Exists 2 then
    let .lam n d b bi := ty.appArg! | return false
    if b.hasLooseBVar 0 && (← isProp d) then return true
    return ← withLocalDecl n bi d fun x => spineDep (b.instantiate1 x) (fuel - 1)
  if let .forallE n d b bi := ty then
    if b.hasLooseBVar 0 && (← isProp d) then return true
    return ← withLocalDecl n bi d fun x => spineDep (b.instantiate1 x) (fuel - 1)
  return false

/-- The goal `ty` with the proofs at its leaves made binders of their own (`genLeaf`), along its
spine of `∧`, guarded `∃ (h : a), _` and `∀ x, _`: `∃ (h : xs.length = 3), ∀ i (h₁ : 0 ≤ i) (h₂ : i <
3), xs[i.toNat]'(… h h₂ …) ≥ 0` ↦ `∃ (h : xs.length = 3), ∀ i, 0 ≤ i → i < 3 → ∀ (hp : i.toNat <
xs.length), xs[i.toNat]'hp ≥ 0`, with `back : new → ty` (proof irrelevance).  The propositional
binders become plain implications: `grind`'s arithmetic normaliser raises `maximum recursion depth`
on a binder with a numeral bound that a proof depends on, in the goal as in hypotheses. -/
private partial def genGoal (ty : Expr) (fuel : Nat := 12) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let ty := ty.headBeta
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!; let b := ty.appArg!
    let ra ← genGoal a (fuel - 1)
    let rb ← genGoal b (fuel - 1)
    if ra.isNone && rb.isNone then return none
    let (a', ba) := ra.getD (a, ← withLocalDeclD `p a fun p => mkLambdaFVars #[p] p)
    let (b', bb) := rb.getD (b, ← withLocalDeclD `p b fun p => mkLambdaFVars #[p] p)
    let ty' := mkAnd a' b'
    let back ← withLocalDeclD `p ty' fun p => do
      mkLambdaFVars #[p] (mkApp4 (mkConst ``And.intro) a b
        (mkApp ba (mkApp3 (mkConst ``And.left) a' b' p)) (mkApp bb (mkApp3 (mkConst ``And.right) a' b' p)))
    return some (ty', back)
  if ty.isAppOfArity ``Exists 2 then
    let a := ty.appFn!.appArg!
    let .lam n _ body bi := ty.appArg! | return none
    unless ← isProp a do return none
    let some (lam', bk) ← withLocalDecl n bi a fun h => do
        let some (b', bb) ← genGoal (body.instantiate1 h) (fuel - 1) | return none
        return some (← mkLambdaFVars #[h] b', ← mkLambdaFVars #[h] bb)
      | return none
    let ty' ← mkAppM ``Exists #[lam']
    let back ← withLocalDeclD `p ty' fun p => do
      let fst ← mkAppM ``exists_prop_fst #[p]
      let snd ← mkAppM ``exists_prop_snd #[p]
      mkLambdaFVars #[p] (← mkAppOptM ``Exists.intro #[some a, some ty.appArg!, some fst, some (mkApp2 bk fst snd).headBeta])
    return some (ty', back)
  if let .forallE n d body bi := ty then
    -- (the premise of an implication `a → b` is not on the spine: only `b` is changed)
    if !body.hasLooseBVars && !(← isProp d) then return none
    let some (lam', bk) ← withLocalDecl n bi d fun x => do
        let some (b', bb) ← genGoal (body.instantiate1 x) (fuel - 1) | return none
        return some (← mkLambdaFVars #[x] b', ← mkLambdaFVars #[x] bb)
      | return none
    let .lam _ _ body' _ := lam' | return none
    let ty' := Expr.forallE n d body' bi
    let back ← withLocalDeclD `p ty' fun p => do
      withLocalDecl n bi d fun x => do
        mkLambdaFVars #[p] (← mkLambdaFVars #[x] (mkApp (mkApp bk x).headBeta (mkApp p x)).headBeta)
    return some (ty', back)
  genLeaf ty

/-- One round of `vreact_bounded` on the hypotheses (steps 1–3); `true` if an instance it added is
itself a guarded or bounded quantifier. -/
private def boundedRound : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let lctx ← getLCtx
  let tgt ← instantiateMVars (← goal.getType)
  let mut have_ : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail then have_ := have_.push (← instantiateMVars d.type)
  -- `have_[base:]`: the parts asserted so far (they stay)
  let base := have_.size
  let mut g := goal
  let mut parts : Array (Expr × Expr) := #[]
  let mut toClear : Array FVarId := #[]
  let mut toDrop : Array (LocalDecl × Expr × Bool) := #[]
  -- the candidates: some binder over `Int` with a guard (cheap filter), or a guarded existential
  let mut cands : Array (LocalDecl × Expr × Bool) := #[]
  for d in lctx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let bounded := ty.find? (fun s => match s with
        | .forallE _ (.const ``Int _) (.forallE ..) _ => true | _ => false) |>.isSome
    let guarded ← hasDepGuard ty
    unless bounded || guarded do continue
    cands := cands.push (d, ty, guarded)
  let mut seen : Array Expr := #[]
  for (d, ty, guarded) in cands do
    -- depended on (by the goal or another local): see 2.
    let used := tgt.containsFVar d.fvarId || lctx.any fun d' =>
      d'.index > d.index && (d'.type.containsFVar d.fvarId || (d'.value?.map (·.containsFVar d.fvarId)).getD false)
    if used then
      toDrop := toDrop.push (d, ty, guarded)
      continue
    -- a second copy of a candidate handled already (it stays, or its parts do), or the original
    -- of a later normalised copy (`vreact_expose`: same name) that is a candidate too
    if seen.contains ty || (!d.userName.hasMacroScopes && cands.any fun (c, _) =>
        c.index > d.index && c.userName == d.userName) then
      toClear := toClear.push d.fvarId
      continue
    seen := seen.push ty
    -- a duplicate of a hypothesis that stays: an asserted part, or a local that is not `d`, not
    -- cleared, not depended on, and not a later candidate
    let isDup (t : Expr) : Bool := (have_.extract base have_.size).contains t ||
      lctx.any fun d' => d'.fvarId != d.fvarId && !d'.isImplementationDetail && d'.type == t &&
        !toClear.contains d'.fvarId && !toDrop.any (·.1.fvarId == d'.fvarId) &&
        !cands.any (fun (c, _) => c.index > d.index && c.fvarId == d'.fvarId)
    let saved ← saveState
    match ← candParts g d.fvarId ty guarded isDup with
    | some (g', ps, tys, clr) =>
      g := g'; parts := parts ++ ps; have_ := have_ ++ tys
      if clr then toClear := toClear.push d.fvarId
    | none => saved.restore
  g ← g.tryClearMany toClear
  if !parts.isEmpty || !toClear.isEmpty then
    for (d, ty, guarded) in toDrop do
      let saved ← saveState
      let some g' ← (try freeGoal g d.fvarId catch _ => pure none) | saved.restore; continue
      g := g'
      -- the normalised copy (same name, later, not depended on itself)
      let copied := lctx.any fun d' => d'.index > d.index && d'.userName == d.userName &&
        !toDrop.any (·.1.fvarId == d'.fvarId)
      if copied then
        if let some g' ← (try some <$> g.clear d.fvarId catch _ => pure none) then g := g'
        continue
      let isDup (t : Expr) : Bool := (have_.extract base have_.size).contains t ||
        lctx.any fun d' => d'.fvarId != d.fvarId && !d'.isImplementationDetail && d'.type == t &&
          !toClear.contains d'.fvarId && !toDrop.any (·.1.fvarId == d'.fvarId)
      let saved ← saveState
      match ← (try candParts g d.fvarId ty guarded isDup catch _ => pure none) with
      | some (g', ps, tys, true) =>
        if let some g'' ← (try some <$> g'.clear d.fvarId catch _ => pure none) then
          g := g''; parts := parts ++ ps; have_ := have_ ++ tys
        else saved.restore
      | _ => saved.restore
  if parts.isEmpty then replaceMainGoal [g]; return false
  let mut targets : Array Expr := #[tgt]
  for d in lctx do
    if !d.isImplementationDetail then targets := targets.push (← instantiateMVars d.type)
  let idxs ← indexTerms targets lctx
  let mut again := false
  for (pf, _) in parts.toList.take 8 do
    for c in idxs do
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
      -- an instance that is itself a guarded or bounded quantifier (`g[1].length === 2 &&
      -- forall(0, 2, c => g[1][c] >= 0)`, a row of a 2-D grid): another round
      if (← g.withContext (hasDepGuard ty)) || (ty.find? (fun s => match s with
          | .forallE _ (.const ``Int _) (.forallE ..) _ => true | _ => false)).isSome then again := true
  replaceMainGoal [g]
  return again

/-- `vreact_bounded`: bounded quantifiers among the hypotheses (`forall(lo, hi, i => P)` is
`∀ i : Int, lo ≤ i → i < hi → P i`, possibly inside guards `∃ (h : a), …` and `∧`).
0. A goal with a propositional binder that a proof depends on (`forall(…)` or a guarded `&&` to
   establish) has its proofs made binders of their own (`genGoal`), and is normalised again.
1. A hypothesis that has one, or a guarded existential whose body indexes with its guard
   (`hasDepGuard`), is replaced by its parts (`candParts`): the guards, the other conjuncts with
   the proofs that use the hypothesis made hypotheses of their own (`abstractProofsUsing`), and the
   quantifiers with their index proofs made non-dependent (`genProofs`).  `grind`'s arithmetic
   normaliser raises `maximum recursion depth` on a binder with a numeral bound that a later proof
   depends on, `∀ i (h : i < 3), … xs[i.toNat]'(… h …) …` (a core Lean 4.35 limitation), and it does
   so on any hypothesis of the context.  A part that duplicates a hypothesis that stays is not
   added (two copies of one precondition, the second made by `vreact_expose`, must not each be
   dropped as a duplicate of the other).
2. A hypothesis only the goal depends on: the proofs in the goal that use it are generalised
   (`freeGoal`); then it is removed if `vreact_expose` made a normalised copy of it (same name;
   replaced by its parts in step 1), otherwise replaced by its own parts like the others.
3. The quantifiers are instantiated at the index terms of the goal, for each whose bounds `omega`
   proves: `grind` instantiates them by E-matching on `xs[i.toNat]`, which `xs[0]` (a numeral
   index, after `Int.toNat 0` is evaluated) does not match.  An instance that is itself guarded or
   bounded (a row `g[1]` of a 2-D grid) gets steps 1–3 again (at most three rounds). -/
elab "vreact_bounded" : tactic => do
  -- 0. the goal: one with a propositional binder that a proof depends on (a bounded quantifier, a
  -- guarded existential) gets its proofs generalised (`genGoal`) and is normalised again
  -- (again after `simp`: `JS.get xs i hp` becomes `xs[i.toNat]'(… hp …)`, whose proof is generalised
  -- in turn, so that the bound is stated in terms of `xs` itself)
  for _ in [0:3] do
    if (← getGoals).isEmpty then return
    let changed ← withMainContext do
      let goal ← getMainGoal
      let tgt ← instantiateMVars (← goal.getType)
      unless ← spineDep tgt do return false
      let some (ty', back) ← (try genGoal tgt catch _ => pure none) | return false
      let g' ← mkFreshExprSyntheticOpaqueMVar ty' (← goal.getTag)
      goal.assign (mkApp back g')
      replaceMainGoal [g'.mvarId!]
      -- conjunctions under the quantifiers become conjuncts of the goal (`vreact_finish` proves
      -- them one by one: `grind` on `∀ i, … → (a ∧ b)` runs out of instances)
      evalTactic (← `(tactic| vreact_try simp (config := { zetaDelta := true, failIfUnchanged := false }) only [vreact_simp, forall_and]))
      return true
    unless changed do break
  -- 1.–3., again for instances that are guarded or bounded quantifiers themselves (at most 3 rounds)
  for _ in [0:3] do
    if (← getGoals).isEmpty then return
    unless ← boundedRound do break

/-- One list operation that is a sub-permutation of its input (`Lists.lean`): the input, and
the proof of `SubPerm e input`. -/
private def subPermStep? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if e.isAppOfArity ``List.filter 3 then
    return some (e.getArg! 2, ← mkAppM ``subPerm_filter #[e.getArg! 1, e.getArg! 2])
  if e.isAppOfArity ``JS.slice 4 then
    return some (e.getArg! 1, ← mkAppM ``subPerm_slice #[e.getArg! 1, e.getArg! 2, e.getArg! 3])
  if e.isAppOfArity ``JS.toSorted 3 then
    return some (e.getArg! 1, ← mkAppM ``subPerm_toSorted #[e.getArg! 1, e.getArg! 2])
  if e.isAppOfArity ``List.reverse 2 then
    return some (e.getArg! 1, ← mkAppM ``subPerm_reverse #[e.getArg! 1])
  if e.isAppOfArity ``List.take 3 then
    return some (e.getArg! 2, ← mkAppM ``subPerm_take #[e.getArg! 1, e.getArg! 2])
  if e.isAppOfArity ``List.drop 3 then
    return some (e.getArg! 2, ← mkAppM ``subPerm_drop #[e.getArg! 1, e.getArg! 2])
  return none

/-- `vreact_subperm`: distinct keys and counts through chains of list operations
(`items.toSorted(cmp).slice(a, b)`, `xs.filter(p).slice(2).toReversed()`, `const`s of them).
For each `Nodup (map f L)` / `Nodup L` of the goal and the hypotheses whose `L` is a chain of
sub-permutations (`filter`, `slice`, `toSorted`, `reverse`, `take`, `drop`) of a list `R` with a
hypothesis `Nodup (map f R)`, add `Nodup (map f L)` (`SubPerm.trans` of the steps, then
`SubPerm.nodup_map`); for each count `(L.filter p).length` of such a chain, add `≤ (R'.filter
p).length` for the lists `R'` of the chain whose count `(R'.filter p)` occurs.  Only facts whose
other side is already present: following a chain to a literal list (a constant of the program)
would make `grind` evaluate it. -/
elab "vreact_subperm" : tactic => withMainContext do
  let goal ← getMainGoal
  let lctx ← getLCtx
  let mut known : Array (Expr × Expr) := #[]
  for d in lctx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    for (pf, pty) in ← hypParts (mkFVar d.fvarId) ty 3 do
      if pty.isAppOfArity ``List.Nodup 2 then known := known.push (pty, pf)
  let mut targets : Array Expr := #[← instantiateMVars (← goal.getType)]
  for d in lctx do
    if !d.isImplementationDetail then targets := targets.push (← instantiateMVars d.type)
  let nodups ← IO.mkRef (#[] : Array Expr)
  let filters ← IO.mkRef (#[] : Array Expr)
  for t in targets do
    forEachExpr t fun e => do
      if e.hasLooseBVars || e.hasMVar then return
      if e.hasAnyFVar (fun fv => !lctx.contains fv) then return
      if e.isAppOfArity ``List.Nodup 2 then
        let l := e.appArg!
        let l := if l.isAppOfArity ``List.map 4 then l.appArg! else l
        if l.isAppOfArity ``List.filter 3 || l.isAppOfArity ``JS.slice 4 || l.isAppOfArity ``JS.toSorted 3 ||
            l.isAppOfArity ``List.reverse 2 || l.isAppOfArity ``List.take 3 || l.isAppOfArity ``List.drop 3 then
          nodups.modify fun a => if a.contains e || a.size ≥ 16 then a else a.push e
      if e.isAppOfArity ``List.filter 3 then
        filters.modify fun a => if a.contains e || a.size ≥ 32 then a else a.push e
  let mut facts : Array Expr := #[]
  -- distinct keys: `mk pf` turns a proof of `Nodup (map f cur)` into one of `Nodup (map f L)`
  for nd in ← nodups.get do
    let x := nd.appArg!
    let (f?, l) := if x.isAppOfArity ``List.map 4 then (some (x.getArg! 2), x.appArg!) else (none, x)
    let mut cur := l
    let mut f := f?
    let mut mk : Expr → MetaM Expr := pure
    for _ in [0:8] do
      if let some (inner, step) ← subPermStep? cur then
        let mk0 := mk
        let isMap := f.isSome
        mk := fun pf => do mk0 (← mkAppM (if isMap then ``SubPerm.nodup_map else ``SubPerm.nodup) #[step, pf])
        cur := inner
      else if let (some fk, true) := (f, cur.isAppOfArity ``List.map 4) then
        -- a map that keeps the key: `fun x => fk (g x)` unfolds to `fk`, or (a map-update by
        -- cases, `x.id === k ? {...x, name} : x`) `∀ x, fk (g x) = fk x` holds by `simp`
        let g := cur.getArg! 2
        let inner := cur.appArg!
        let ty ← whnfR (← inferType inner)
        unless ty.isAppOfArity ``List 1 do break
        let α := ty.appArg!
        let keep? ← (do
            unless ← isDefEq (← inferType cur) ty do return none
            let stmt ← withLocalDeclD `x α fun xv => do
              mkForallFVars #[xv] (← mkEq (mkApp fk (mkApp g xv)).headBeta (mkApp fk xv).headBeta)
            let m ← mkFreshExprMVar stmt
            let saved ← getGoals
            let ok ← (do
                setGoals [m.mvarId!]
                evalTactic (← `(tactic| (intro x; first | rfl | (simp only [vreact_simp]; done))))
                pure true) <|> pure false
            setGoals saved
            if ok then return some (← instantiateMVars m) else return none : TacticM (Option Expr))
        let mk0 := mk
        if let some hfg := keep? then
          mk := fun pf => do mk0 (← mkAppOptM ``nodup_map_map_of_keep #[none, none, some fk, some g, some inner, some hfg, some pf])
        else
          let fk' ← withLocalDeclD `x α fun xv => do
            mkLambdaFVars #[xv] (← whnfR (mkApp fk (mkApp g xv)).headBeta)
          mk := fun pf => do mk0 (← mkAppOptM ``nodup_map_map_comp #[none, none, none, some fk, some g, some inner, some pf])
          f := some fk'
        cur := inner
      else break
      let want ← match f with
        | some fk => mkAppM ``List.Nodup #[← mkAppM ``List.map #[fk, cur]]
        | none => mkAppM ``List.Nodup #[cur]
      let mut hit : Option Expr := none
      for (kty, kpf) in known do
        if ← withReducible (isDefEq kty want) then hit := some kpf; break
      if let some kpf := hit then
        if let some pf ← (try some <$> mk kpf catch _ => pure none) then facts := facts.push pf
        break
  -- counts
  let fs ← filters.get
  for fl in fs do
    let p := fl.getArg! 1
    let mut cur := fl.getArg! 2
    let mut sp? : Option Expr := none
    for _ in [0:8] do
      let some (inner, step) ← subPermStep? cur | break
      let sp ← match sp? with | none => pure step | some sp => mkAppM ``SubPerm.trans #[sp, step]
      sp? := some sp
      cur := inner
      -- a count over `cur` with the same predicate occurs
      let mut hit := false
      for fl' in fs do
        if ← withReducible (isDefEq fl' (← mkAppM ``List.filter #[p, cur])) then hit := true; break
      if hit then facts := facts.push (← mkAppM ``SubPerm.length_filter_le #[p, sp])
  if facts.isEmpty then return
  let mut have_ : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail then have_ := have_.push (← instantiateMVars d.type)
  let mut g := goal
  for pf in facts do
    let ty ← instantiateMVars (← inferType pf)
    if have_.contains ty then continue
    have_ := have_.push ty
    let (_, g') ← (← g.assert (← mkFreshUserName `hsub) ty pf).intro1P
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

open Lean Meta in
/-- Arithmetic arguments of calls of the program's functions (`upd s k (q - 1)`, a call of an
`@opaque` function whose contracts are hypotheses), generalised to fresh variables with their
equations (`hx : q - 1 = x`).  `grind`'s arithmetic normaliser rewrites `q - 1` inside such a call
wherever it occurs, also under a bounded quantifier whose index proofs mention the call
(`(upd s k (q - 1)).m.keys[i]'h` of a contract `forall(0, n, (i) => …)`), and there it ran into
Lean's recursion limit; with `x` for `q - 1` the call is an atom again.  none if there is no
such argument. -/
private def genArithArgs (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let lctx ← getLCtx
  let mut targets := #[← instantiateMVars (← g.getType)]
  for d in lctx do
    if !d.isImplementationDetail && !d.isLet then targets := targets.push (← instantiateMVars d.type)
  let found ← IO.mkRef (#[] : Array Expr)
  let isArith (a : Expr) : Bool :=
    a.isAppOfArity ``HSub.hSub 6 || a.isAppOfArity ``HAdd.hAdd 6 || a.isAppOfArity ``HMul.hMul 6 ||
      a.isAppOfArity ``Neg.neg 3
  for tgt in targets do
    forEachExpr tgt fun e => do
      if e.hasLooseBVars || e.hasMVar then return
      -- binders visited by `forEachExpr` become temporary fvars: only closed terms
      if e.hasAnyFVar (fun fv => !lctx.contains fv) then return
      let .const fn _ := e.getAppFn | return
      unless (`VTS).isPrefixOf fn do return
      for a in e.getAppArgs do
        if isArith a && !(← found.get).contains a then found.modify (·.push a)
  let args ← found.get
  if args.isEmpty then return none
  let hyps := lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.fvarId
  let gargs := args.map fun a => ({ expr := a, xName? := `x, hName? := `hx } : GeneralizeArg)
  let (_, _, g') ← g.generalizeHyp gargs hyps
  return some g'

open Lean Meta Elab Tactic in
/-- The cheap alternatives (`done`, `grind`, `omega`) on the main goal.  `none` if one closes
it, otherwise the error to report: `grind`'s (it shows the hypotheses and the case it got
stuck in) — never a later alternative's message such as `simp_all made no progress`. -/
private def finishCheap : TacticM (Option Exception) := withMainContext do
  let goal ← getMainGoal
  if (← attemptClose (← `(tactic| done))).isNone then return none
  let grindErr ← attemptClose (← `(tactic| grind))
  if grindErr.isNone then return none
  -- `grind` at the recursion limit: again with the arithmetic arguments of calls generalised
  if grindErr.any (·.isRuntime) then
    let r ← tryTactic do
      let some g' ← genArithArgs (← getMainGoal) | throwError "no arithmetic arguments"
      replaceMainGoal [g']
      evalTactic (← `(tactic| grind))
      unless (← getUnsolvedGoals).isEmpty do throwError "unsolved goals"
    if r.isNone then return none
  if (← attemptClose (← `(tactic| omega))).isNone then return none
  match grindErr with
  | some e =>
    -- a runtime exception is reported as an ordinary error (the caller may still try
    -- the other conjuncts, and `try … catch` does not catch runtime exceptions).
    -- Not Lean's own wording: the report would read that as an aborted declaration.
    if e.isRuntime then
      -- (with its message context: the goal may be gone from the state the report is made in)
      return some (.error (← getRef) (← addMessageContext m!"vreact_auto could not prove the goal (grind stopped at Lean's recursion limit){indentD (MessageData.ofGoal goal)}"))
    return some e
  | none => return some (.error (← getRef) (← addMessageContext m!"vreact_auto could not prove the goal{indentD (MessageData.ofGoal goal)}"))

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
/-- `σ.mode`, `o.inner.mode`: projections (at most four) of a local. -/
private partial def isFieldChain (e : Expr) (fuel : Nat := 4) : MetaM Bool := do
  if fuel == 0 then return false
  let .const fn _ := e.getAppFn | return false
  unless (← getProjectionFnInfo? fn).isSome && e.getAppNumArgs ≥ 1 do return false
  let a := e.appArg!
  if a.isFVar then return true
  isFieldChain a (fuel - 1)

open Lean Meta in
/-- Terms of the goal (then of the hypotheses) whose type is a small enumeration or union (a
non-recursive inductive type without parameters or indices, with 2–8 constructors, other than
`Bool`/`Int`): locals, and fields of locals (`σ.mode`, `o.inner.mode`), in order of occurrence.  (After `split`
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
       | _ => isFieldChain e
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
establish, at most 16 values: a board of 9 or 16 cells): introduced, and split into the cases `i = lo`, …, `i = hi - 1`
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
      unless lo < hi && hi - lo ≤ 16 do continue
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

open Lean Meta in
/-- Case splits on the `if`s (and `match`es) of hypotheses, one hypothesis after the other, at most
`fuel` splits and `cap` goals: a guarded Bool function of a contract (`m.has(k) && … m.get(k)!.qty …`,
a dependent `if h : … then … (o.get ⋯) … else false`, which `dite_eq_ite` cannot turn into a
conjunction) or an `if`-chain of a body that the `split` of a `match` on it moved into an
equation `heq : (if … then … else …).get k = some p`: `grind` does not split inside those, and
its arithmetic under the dependent proofs ran into the recursion limit.  none if no hypothesis
has one. -/
private def splitHyps? (g : MVarId) (fuel : Nat := 8) (cap : Nat := 16) : MetaM (Option (List MVarId)) := do
  let step (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      unless ← isProp d.type do continue
      if let some gs ← splitLocalDecl? g d.fvarId then return some gs
    return none
  let some first ← step g | return none
  let mut done : List MVarId := []
  let mut todo := first
  let mut n := fuel
  while !todo.isEmpty do
    let gi :: rest := todo | break
    todo := rest
    if n == 0 || done.length + todo.length + 1 ≥ cap then
      done := done ++ [gi]
      continue
    match ← step gi with
    | some gs => n := n - 1; todo := gs ++ todo
    | none => done := done ++ [gi]
  return some done

open Lean Meta Elab Tactic in
/-- `vreact_finish` (see `finishCore`), with fallbacks for the goals it fails on, each case
normalised again and finished at most `depth` levels deep:
* a conjunction: the fallbacks on each conjunct that needs them (no level used);
* a guarded existential goal `∃ (h : a), b h`: `a`, then `b h` (`splitExistsProp?`);
* a bounded quantifier with numeral bounds: one case per value (`enumBounded?`);
* a hypothesis with an `if` or `match`: one case per branch (`splitHyps?`);
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
      evalTactic (← `(tactic| vreact_splits))
      evalTactic (← `(tactic| all_goals vreact_norm))
      evalTactic (← `(tactic| all_goals vreact_memmap))
      evalTactic (← `(tactic| all_goals vreact_keyfacts))
      evalTactic (← `(tactic| all_goals vreact_bounded))
      evalTactic (← `(tactic| all_goals vreact_subperm))
      for gj in ← getGoals do
        setGoals [gj]
        vreactFinishAux (depth - 1)
    setGoals []
  -- a conjunction: the fallbacks on each conjunct (an invariant `(cells.length === 9 && forall(0,
  -- 9, …)) ∧ (turn === 1 || turn === 2)`), at the same depth (a conjunct is not a conjunction)
  let conj ← conjunctGoals g
  if conj.length ≥ 2 then
    if (← tryTactic do
        for gi in conj do
          setGoals [gi]
          vreactFinishAux depth
        setGoals []).isNone then return
    s.restore
  -- guarded existentials, bounded quantifiers
  if (← tryTactic do
      let some goals ← splitExistsProp? g | throwError "no"
      finishAll goals).isNone then return
  s.restore
  if (← tryTactic do
      let some goals ← enumBounded? g | throwError "no"
      finishAll goals).isNone then return
  s.restore
  -- `if`s in hypotheses
  if (← tryTactic do
      let some goals ← splitHyps? g | throwError "no"
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

open Lean Meta Elab Tactic in
/-- `vreact_open`: make the calls of program functions with contracts that occur under a binder of
the goal closed, so that `vreact_contracts` can instantiate their contracts (see "Calls under
binders" in `Contracts.lean`): substitute a timer callback's equation `t = fun _ => …` (and
normalise), open `∃` hypotheses, introduce `∀`/`→` and split `∧` of the goal — each only where
such a call is under the binder.  Does nothing on a goal without one. -/
elab "vreact_open" : tactic => withMainContext do
  let env ← getEnv
  let g ← getMainGoal
  let bound ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    if targetOpens env tgt then return true
    (← getLCtx).anyM fun d => do
      if d.isImplementationDetail || d.isLet then return false
      let ty ← instantiateMVars d.type
      return existsOpens env ty || (ty.isEq && hasBoundCall env ty)
  unless bound do return
  let mut g := g
  let mut substituted := false
  repeat
    let some g' ← substBoundFnEq? g | break
    g := g'
    substituted := true
  replaceMainGoal [g]
  if substituted then
    -- the callback applied to its event: beta-reduce, push the record projections through
    evalTactic (← `(tactic| vreact_norm))
    if (← getUnsolvedGoals).isEmpty then return
  g ← getMainGoal
  repeat
    let some g' ← casesBoundExists? g | break
    g := g'
  replaceMainGoal (← openBoundTarget g)

/-- `vreact_auto` without its last step: everything before `vreact_finish`.  The goals it leaves are
the cases of the obligation (the branches of the `if`s and `match`es that `vreact_splits` split),
each normalised and with its contract instances and helper facts. -/
syntax "vreact_prep" : tactic
macro_rules
  | `(tactic| vreact_prep) => `(tactic|
      (intros
       vreact_expose
       vreact_contracts
       vreact_splits
       all_goals vreact_norm
       -- calls under binders (the updates of a robust outcome, `map`/`every` lambdas)
       all_goals vreact_open
       all_goals vreact_contracts
       all_goals vreact_norm
       all_goals (
         vreact_splits
         all_goals vreact_norm
         all_goals vreact_open
         -- calls exposed by the last split (e.g. in match arms of a transparent reducer)
         all_goals vreact_contracts
         all_goals vreact_norm
         all_goals vreact_memmap
         all_goals vreact_keyfacts
         all_goals vreact_bounded
         all_goals vreact_subperm)))

syntax "vreact_auto" : tactic
macro_rules
  | `(tactic| vreact_auto) => `(tactic|
      (vreact_prep
       all_goals vreact_finish))

open Lean Meta Elab Tactic in
/-- Run `k` with a budget of its own: `b` heartbeats (Lean's raw count, as `IO.getNumHeartbeats`),
counted from now (see `vreact_ob`). -/
def withHeartbeatBudget {α : Type} (b : Nat) (k : TacticM α) : TacticM α :=
  controlAt CoreM fun runInBase => do
    let now ← IO.getNumHeartbeats
    withReader (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := b }) (runInBase k)

open Lean Meta Elab Tactic in
/-- Where `vreact_auto` fails on the main goal, after it ran out of the obligation's budget
`budget` (Lean's raw heartbeats): `vreact_prep` (with a quarter of the budget), then
`vreact_finish` on each case it leaves alone, smallest goal first, with a tenth of the budget
each and half of it in all, until a case fails.  The message says how many cases were proved,
did not finish or were not tried, and shows the error of the case that failed (`grind`'s goal),
or else the goal of the first case that did not finish.  `none` if the goal has no cases (or
`vreact_prep` itself did not finish).  Only a diagnosis: the state (and message log) is
restored, and the obligation stays failed — a case proved here proves nothing about the
obligation, whose own run did not finish. -/
def timeoutCases (budget : Nat) : TacticM (Option MessageData) := do
  let s ← saveState
  let log ← Core.getMessageLog
  try
    let prep ← tryCatchRuntimeEx
      (do withHeartbeatBudget (budget / 4) (evalTactic (← `(tactic| vreact_prep))); pure true)
      (fun _ => pure false)
    unless prep do return none
    let goals ← getUnsolvedGoals
    let n := goals.length
    if n < 2 then return none
    let mut sized : Array (Nat × Nat × MVarId) := #[]
    let mut i : Nat := 0
    for g in goals do
      sized := sized.push ((← instantiateMVars (← g.getType)).sizeWithoutSharing, i, g)
      i := i + 1
    let sorted := sized.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
    let per := budget / 10
    let start ← IO.getNumHeartbeats
    let mut proved : Nat := 0
    let mut slow : Array MVarId := #[]
    let mut tried : Nat := 0
    let mut failed : Option (MVarId × MessageData) := none
    for (_, _, g) in sorted do
      if (← IO.getNumHeartbeats) - start ≥ budget / 2 then break
      tried := tried + 1
      let gs ← saveState
      setGoals [g]
      Core.resetMessageLog
      let r ← tryCatchRuntimeEx
        (do
          withHeartbeatBudget per vreactFinish
          unless (← getUnsolvedGoals).isEmpty do throwError "unsolved goals"
          if let some m := (← Core.getMessageLog).reportedPlusUnreported.toList.find? (·.severity == .error) then
            throw (.error .missing m.data)
          pure none)
        (fun ex => pure (some ex))
      match r with
      | none => proved := proved + 1
      | some ex =>
        if ex.isMaxHeartbeat then slow := slow.push g
        else
          -- the message, with the context of the failed run (its goals are gone afterwards)
          let msg ← addMessageContext ex.toMessageData
          failed := some (g, msg)
      gs.restore
      if failed.isSome then break
    let notTried : Nat := n - tried
    let rest := if notTried > 0 then m!" ({notTried} not tried)" else m!""
    let name (g : MVarId) : MetaM MessageData := do
      let t ← g.getTag
      return if t.isAnonymous then m!"(unnamed)" else m!"{t}"
    -- (the names as the translation makes them: a `switch` on a union or an enum is a `match`
    -- with one alternative per `case` label in source order — Lean expands `| .a | .b =>` — and a
    -- last `_` for `default`; a `switch` on a number or a string is a chain of `if`s, one per body)
    let head := m!"The goal splits into {n} cases. A case's name lists the branches that lead to it, \
      outermost first: `isTrue`/`isFalse` are the two branches of an `if` (a `switch` on a number or a \
      string is a chain of `if`s, one per body), `h_k` is the k-th alternative of a `match` (a `switch` \
      on a union or an enum has one per `case` label, in the order written, then one for the rest: \
      `default`, wherever it is written); conditions in the translation (such as the sign test of `%`) \
      split the same way. Each case alone, smallest first, with up to {per / 1000} heartbeats:"
    match failed, slow[0]? with
    | some (g, msg), _ =>
      return some m!"{head} {proved} proved, {slow.size} did not finish, then case {← name g} \
        failed{rest}:\n{msg}"
    | none, some g =>
      return some m!"{head} {proved} proved, {slow.size} did not finish{rest}. The first that did \
        not finish, case {← name g}:\n{← addMessageContext (MessageData.ofGoal g)}"
    | none, none =>
      if notTried == 0 then
        return some m!"{head} all {n} proved, but together they need more than the obligation's budget."
      return some m!"{head} {proved} proved{rest}."
  finally
    s.restore
    Core.setMessageLog log

end VReact
