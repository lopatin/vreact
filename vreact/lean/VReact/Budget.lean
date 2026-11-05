import Lean
/-!
# `vreact_ob` — one proof obligation: its own heartbeat budget, and its result as a message

Every generated obligation is `(/-⟦obN⟧-/ by vreact_ob vreact_auto)`.

**Budget.** Lean's `maxHeartbeats` is a budget per *command*: all `by` blocks of one
declaration (e.g. every handler obligation inside a component's `render`) share it, and
running out raises a *runtime* exception that `first`/`try` do not catch, so it aborts the
whole declaration: later obligations never run, and the error lands on whichever obligation
happened to be running. `vreact_ob tac` runs `tac` with a fresh budget of `vreact.heartbeats`
(in thousands, like `maxHeartbeats`; `"heartbeats"` in vreact.json, default 1000000). The
generated files set `maxHeartbeats` of each file to cover all obligations of its largest
declaration, so the command budget only bounds the non-obligation work.

**Result.** The obligation's outcome is a message at the `vreact_ob` token:

* proved — an information `vreact:ok` (the *positive evidence* the report requires: an
  obligation without it counts as not checked, never as proved);
* failed — a **warning** `vreact: <why>` with the failure text and the goal; the goal is
  admitted with `sorry`. Failures are: the tactic failed (any exception, also the heartbeat
  limit or the maximal recursion depth), goals were left, the automation logged an error,
  or the proof it produced uses `sorry` that the goal did not contain;
* blocked — a **warning** `vreact:blocked <why>` when it failed on a goal that depends on
  `sorry` from elsewhere (an obligation above that failed, a declaration with an error, a
  `hole()`): the goal itself mentions `sorry`, or Lean hid the automation's error because it
  does (Lean does not show errors that mention such a `sorry`). The goal is admitted too;
  the report counts the obligation as not checked (fix the failure it depends on first).

Neither is a Lean error, so the module still builds and the modules importing it are checked
too; the admitted goal shows as `sorryAx` in the axioms of everything that depends on it.
Messages the automation itself logged are kept, except errors (they are the failure) and
messages that look like `vreact_ob`'s own results (`vreact:…`): a simproc or tactic running
inside an obligation cannot forge its evidence.
-/

register_option vreact.heartbeats : Nat := {
  defValue := 1000000
  descr := "heartbeat budget (in thousands, like maxHeartbeats) of each vreact proof obligation"
}

namespace VReact
open Lean Elab Tactic Meta

syntax (name := vreactOb) "vreact_ob " tacticSeq : tactic

/-- Whether a (new) constant's value uses `sorryAx`, also through other constants added
during the same obligation (auxiliary lemmas of the automation). -/
private partial def newSorry (old : Environment) (e : Expr) : MetaM Bool := do
  let seen ← IO.mkRef ({} : NameSet)
  let rec go (e : Expr) : MetaM Bool := do
    if e.hasSorry then return true
    for c in e.getUsedConstants do
      if old.contains c || (← seen.get).contains c then continue
      seen.modify (·.insert c)
      let v? := match (← getEnv).find? c with
        | some (.thmInfo t) => some t.value
        | some (.defnInfo d) => some d.value
        | some (.opaqueInfo o) => some o.value
        | _ => none
      if let some v := v? then
        if ← go v then return true
    return false
  go e

/-- The goal, its hypotheses included, mentions `sorryAx` (from a failure above it). -/
private def goalHasSorry (g : MVarId) : MetaM Bool := g.withContext do
  if (← instantiateMVars (← g.getType)).hasSorry then return true
  for d in ← getLCtx do
    if (← instantiateMVars d.type).hasSorry then return true
    if let some v := d.value? then
      if (← instantiateMVars v).hasSorry then return true
  return false

/-- `vreact:…` texts are `vreact_ob`'s own results; nobody else may log them inside it. -/
private def isResultText (m : Message) : BaseIO Bool := do
  return ((← m.data.toString).dropWhile Char.isWhitespace).startsWith "vreact:"

/-- Why an obligation was not proved; `blocked`: its goal depends on `sorry` from elsewhere. -/
private structure Failure where
  why : MessageData
  blocked : Bool := false

@[tactic vreactOb] def evalVreactOb : Tactic := fun stx => do
  let ref ← getRef
  let goals ← getGoals
  let saved ← Tactic.saveState
  let envBefore ← getEnv
  let sorryBefore ← goals.anyM (fun g => goalHasSorry g)
  let budget := vreact.heartbeats.get (← getOptions) * 1000
  -- the automation's messages are collected apart from the file's
  let outer ← Core.getMessageLog
  Core.resetMessageLog
  -- (also among messages already marked as reported)
  let loggedError : TacticM (Option MessageData) := do
    return (← Core.getMessageLog).reportedPlusUnreported.toList.find? (·.severity == .error) |>.map (·.data)
  let failure : Option Failure ← tryCatchRuntimeEx
    (do
      controlAt CoreM fun runInBase => do
        let now ← IO.getNumHeartbeats
        withReader (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := budget })
          (runInBase (evalTactic stx[1]))
      let rest ← getUnsolvedGoals
      unless rest.isEmpty do
        return some { why := m!"unsolved goals\n{goalsToMessageData rest}" }
      if let some e ← loggedError then
        return some { why := e }
      unless sorryBefore do
        for g in goals do
          if ← newSorry envBefore (← instantiateMVars (mkMVar g)) then
            return some { why := m!"the automation closed the goal with `sorry`" }
      return none)
    (fun ex => do
      if ex.isMaxHeartbeat then
        return some { why := m!"(deterministic) timeout: the automation did not finish within this \
          obligation's budget of {budget / 1000} heartbeats (set \"heartbeats\" in vreact.json to change it)" }
      -- an abort carries no text: the error logged before it says why; when there is none,
      -- Lean hid it, which it does for errors that mention `sorry`
      if let .internal id _ := ex then
        if let some e ← loggedError then
          return some { why := e }
        return some { why := m!"the automation stopped ({← id.getName}); Lean hid its error, which \
          mentions `sorry`", blocked := true }
      return some { why := ex.toMessageData })
  let inner ← Core.getMessageLog
  if failure.isSome then saved.restore (restoreInfo := true) else Core.setMessageLog outer
  for m in inner.toList do
    unless m.severity == .error || (← isResultText m) do logMessage m
  match failure with
  | none => logInfoAt ref "vreact:ok"
  | some f =>
    -- the goal as the obligation stated it, unless the failure text shows one already
    let shown ← (← addMessageContext f.why).toString
    let goal := if shown.contains '⊢' then m!"" else m!"\n{goalsToMessageData goals}"
    if f.blocked || sorryBefore || f.why.hasSyntheticSorry then
      logWarningAt ref m!"vreact:blocked the goal depends on `sorry` from elsewhere (an obligation \
        that failed, a declaration with an error, or a hole()), so this obligation could not be \
        checked; fix that first\n{f.why}{goal}"
    else
      logWarningAt ref m!"vreact: {f.why}{goal}"
    for g in goals do admitGoal g
    setGoals []

end VReact
