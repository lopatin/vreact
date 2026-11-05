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
   integer arithmetic + case splitting), falling back to `omega` / `simp_all`;
   if all fail on a conjunction, prove the conjuncts separately; a failure
   reports `grind`'s goal (`vreact_finish`).

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
-- quantifiers over a `map` result: `∀ c ∈ xs.map f, P c` ↦ `∀ a ∈ xs, P (f a)` (before
-- `mem_map` rewrites the membership); then conditional record updates (`pushProjIte` in
-- `Simprocs.lean`) collapse field by field with `ite_self`
attribute [vreact_simp ↓] List.forall_mem_map
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

/-- Normalise hypotheses and goal with the model's simp set. -/
macro "vreact_norm" : tactic => `(tactic|
  (try simp (config := { zetaDelta := true, failIfUnchanged := false }) only [vreact_simp] at *))

open Lean Meta Elab Tactic in
/-- Close the main goal (normalised) by `grind`, `omega` or `simp_all`.  Returns the error
to report when all of them fail: `grind`'s (it shows the hypotheses and the case it got
stuck in) or, if `grind` did not run to a verdict, one that shows the goal — never the last
alternative's message such as `simp_all made no progress`. -/
private def finishOne : TacticM (Option Exception) := withMainContext do
  let goal ← getMainGoal
  let s ← saveState
  let attempt (tac : TSyntax `tactic) : TacticM (Option Exception) := do
    try
      -- like the alternatives of `first`: no error recovery (an error must not be logged
      -- and the goal admitted; it must make us try the next alternative)
      withoutRecover (evalTactic tac)
      if (← getUnsolvedGoals).isEmpty then return none
      throwError "unsolved goals"
    catch e =>
      s.restore
      return some e
  if (← attempt (← `(tactic| done))).isNone then return none
  let grindErr ← attempt (← `(tactic| grind))
  if grindErr.isNone then return none
  if (← attempt (← `(tactic| omega))).isNone then return none
  if (← attempt (← `(tactic| (simp_all; done)))).isNone then return none
  if (← attempt (← `(tactic| (simp_all; grind)))).isNone then return none
  match grindErr with
  | some e => return some e
  | none => return some (.error (← getRef) m!"vreact_auto could not prove the goal{indentD (MessageData.ofGoal goal)}")

open Lean Meta Elab Tactic in
/-- `vreact_finish`: close a normalised goal; when that fails on a conjunction, prove the
conjuncts one by one (smaller goals, and the report names only the conjuncts that fail). -/
partial def vreactFinish : TacticM Unit := do
  let some err ← finishOne | return
  let g ← getMainGoal
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  if tgt.isAppOfArity ``And 2 then
    let [g1, g2] ← g.apply (mkConst ``And.intro) | throw err
    let mut firstErr : Option Exception := none
    for gi in [g1, g2] do
      setGoals [gi]
      try vreactFinish catch e => if firstErr.isNone then firstErr := some e
    setGoals []
    if let some e := firstErr then throw e
  else throw err

elab "vreact_finish" : tactic => vreactFinish

syntax "vreact_auto" : tactic
macro_rules
  | `(tactic| vreact_auto) => `(tactic|
      (intros
       vreact_expose
       vreact_contracts
       (repeat' split)
       all_goals vreact_norm
       all_goals vreact_contracts
       all_goals vreact_norm
       all_goals (
         (repeat' split) <;> vreact_norm
         -- calls exposed by the last split (e.g. in match arms of a transparent reducer)
         all_goals vreact_contracts
         all_goals vreact_norm
         all_goals vreact_finish)))

end VReact
