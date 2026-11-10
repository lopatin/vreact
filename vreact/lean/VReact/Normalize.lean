import Lean
import VReact.Tactic
/-!
# `vreact_normalize` — contracts in the normal form of the goals

Callers of an `@opaque` function reason through its postcondition.  Goals are
normalised by `vreact_norm` (definitions unfolded, membership/`Nodup`
distributed over list operations, Bool comparisons turned into propositions);
a postcondition instantiated by `grind` must be in the *same* normal form to be
useful.  `vreact_normalize thm as thm'` simp-normalises the statement of `thm`
with the `vreact_simp` set and adds it as `thm'` (proved from `thm`).
-/
namespace VReact
open Lean Elab Command Meta

elab "vreact_normalize " src:ident " as " dst:ident : command => do
  liftTermElabM do
    let srcName ← realizeGlobalConstNoOverloadWithInfo src
    let some ci := (← getEnv).find? srcName | throwError "unknown constant {srcName}"
    let some ext ← getSimpExtension? `vreact_simp | throwError "vreact_simp simp set not found"
    let thms ← ext.getTheorems
    let ctx ← Simp.mkContext (config := { zetaDelta := true }) (simpTheorems := #[thms])
      (congrTheorems := (← getSimpCongrTheorems))
    let (r, _) ← simp ci.type ctx
    let value ← match r.proof? with
      | some p => mkAppM ``Eq.mp #[p, mkConst srcName (ci.levelParams.map mkLevelParam)]
      | none => pure (mkConst srcName (ci.levelParams.map mkLevelParam))
    let dstName := dst.getId
    addDecl <| Declaration.thmDecl {
      name := dstName, levelParams := ci.levelParams, type := r.expr, value := value }

end VReact
