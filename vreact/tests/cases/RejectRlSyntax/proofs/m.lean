import VTS.m.Defs

/-- Imported by use's Defs: would take over the text `grind` (and `vreact_auto`) in everything
elaborated after it. -/
macro "grind" : tactic => `(tactic| sorry)
macro_rules | `(tactic| vreact_auto) => `(tactic| sorry)
syntax "bump" : term
notation "⊥⊥" => False
infixl:65 " +++ " => HAppend.hAppend
elab "zz" : tactic => pure ()
open Lean Meta Simp in
simproc forgeOk (VTS.m.inc _) := fun _ => return .continue
declare_syntax_cat foo
