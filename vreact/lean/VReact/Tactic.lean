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
/-- `simp … at *` skips hypotheses that other locals depend on.  A render-level
`const cur = xs[i]` is `let cur := JS.get xs i (proof)`, and that proof uses the
invariant `hinv` (or the precondition `hpre`), so `hinv` would stay folded for every
later obligation.  Add a copy of each such hypothesis; `simp` normalises the copy. -/
elab "vreact_expose" : tactic => withMainContext do
  let decls := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
  let mut g ← getMainGoal
  for d in decls do
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let mut used := false
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
def vreactFinish : TacticM Unit := do
  let some err ← finishCheap | return
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
    let some err ← finishSlow err | return
    if n ≤ 1 then throw err
  let mut firstErr : Option Exception := none
  for gi in ← conjunctGoals g do
    setGoals [gi]
    let some e ← finishCheap | continue
    let some e ← finishSlow e | continue
    if firstErr.isNone then firstErr := some e
  setGoals []
  if let some e := firstErr then throw e

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
         all_goals vreact_finish)))

end VReact
