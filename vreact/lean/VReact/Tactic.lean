import VReact.Core
import VReact.Attr
import VReact.Lists
import VReact.Contracts
import VReact.Simprocs
/-!
# `vreact_auto` — the default discharger for every generated proof obligation

1. introduce binders, unfold generated definitions and the model
   (`@[vreact_simp]`), and let-bound locals (`zetaDelta`);
2. split `if`/`match` in the goal, normalise again;
3. close each case with `grind` (congruence closure + E-matching + linear
   integer arithmetic + case splitting), falling back to `omega` / `simp_all`.

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

/-- Normalise hypotheses and goal with the model's simp set. -/
macro "vreact_norm" : tactic => `(tactic|
  (try simp (config := { zetaDelta := true, failIfUnchanged := false }) only [vreact_simp] at *))

syntax "vreact_auto" : tactic
macro_rules
  | `(tactic| vreact_auto) => `(tactic|
      (intros
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
         all_goals (first
           | done
           | grind
           | omega
           | (simp_all; done)
           | (simp_all; grind)))))

end VReact
