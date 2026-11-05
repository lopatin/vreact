import Lean
/-!
# `vreact_ob` — one heartbeat budget per proof obligation

Every generated obligation is `(/-⟦obN⟧-/ by vreact_ob vreact_auto)`.

Lean's `maxHeartbeats` is a budget per *command*: all `by` blocks of one
declaration (e.g. every handler obligation inside a component's `render`) share
it, and running out raises a *runtime* exception that `first`/`try` do not
catch, so it aborts the whole declaration: later obligations never run, and the
error lands on whichever obligation happened to be running.

`vreact_ob tac` runs `tac` with a fresh budget of `vreact.heartbeats` (in
thousands, like `maxHeartbeats`; `"heartbeats"` in vreact.json, default
1000000).  If `tac` exceeds it (or the maximal
recursion depth), the runtime exception becomes an ordinary error reported at
this obligation and the goal is closed with `sorry` (so the declaration is
reported as not verified), and elaboration continues with the next obligation.
Ordinary tactic failures are passed on unchanged.  The generated files set
`maxHeartbeats` of each file to cover all obligations of its largest
declaration, so the command budget only bounds the non-obligation work.
-/

register_option vreact.heartbeats : Nat := {
  defValue := 1000000
  descr := "heartbeat budget (in thousands, like maxHeartbeats) of each vreact proof obligation"
}

namespace VReact
open Lean Elab Tactic

syntax (name := vreactOb) "vreact_ob " tacticSeq : tactic

@[tactic vreactOb] def evalVreactOb : Tactic := fun stx => do
  let ref ← getRef
  let goals ← getGoals
  let saved ← Tactic.saveState
  let budget := vreact.heartbeats.get (← getOptions) * 1000
  tryCatchRuntimeEx
    (controlAt CoreM fun runInBase => do
      let now ← IO.getNumHeartbeats
      withReader (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := budget })
        (runInBase (evalTactic stx[1])))
    (fun ex => do
      unless ex.isRuntime do throw ex
      saved.restore (restoreInfo := true)
      let what := if ex.isMaxHeartbeat then
          m!"(deterministic) timeout: the automation did not finish within this obligation's \
            budget of {budget / 1000} heartbeats (set \"heartbeats\" in vreact.json to change it)"
        else ex.toMessageData
      logErrorAt ref m!"vreact: {what}"
      for g in goals do admitGoal g
      setGoals [])

end VReact
