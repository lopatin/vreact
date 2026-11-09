import Lean
import VReact.Tactic
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

The count is per obligation also when Lean elaborates the declarations of a file in parallel:
`IO.getNumHeartbeats` is the current thread's counter, and an obligation's tactic runs on one
thread.  (Measured: three copies of a 740k-heartbeat obligation in one file used the same count,
±0.02%, in parallel and sequentially.)  The one exception is the cost of realizing an auxiliary
declaration several obligations share (equation lemmas, `match` splitters), which is paid by the
first obligation that needs it (about 0.6% there).  A copy of a theorem placed after the original
`f.post` is not comparable: `vreact_contracts` adds `f.post` as a fact for the call of `f`.

**Result.** The obligation's outcome is a message at the `vreact_ob` token:

* proved — an information `vreact:ok` (the *positive evidence* the report requires: an
  obligation without it counts as not checked, never as proved);
* failed — a **warning** `vreact: <why>` with the failure text and the goal; the goal is
  admitted with `sorry`. Failures are: the tactic failed (any exception, also the heartbeat
  limit or the maximal recursion depth), goals were left, the automation logged an error,
  or the proof it produced uses a `sorry` it made itself (also in an auxiliary lemma).
  When `vreact_auto` runs out of the budget, the text also says where it fails
  (`timeoutCases` in `Tactic.lean`): each case of the goal is tried alone, and the goal of
  the case that fails (or the first that does not finish) is shown — a diagnosis only, with
  up to 0.85 budgets more; the obligation stays failed;
* blocked — a **warning** `vreact:blocked <why>` when the obligation depends on `sorry` from
  elsewhere (an obligation above that failed, a declaration with an error, a `hole()`): the
  proof the automation found uses such a `sorry` (it is in the goal or its hypotheses, or in
  a definition the proof unfolded — a proof through the admitted proof of a false statement
  proves nothing), or the automation failed on a goal that mentions one, or Lean hid the
  automation's error because it does (Lean does not show errors that mention such a `sorry`),
  or it failed on a goal whose (reducible) definitions unfold to a `sorry` that stands for
  data (a `hole()`: the automation cannot know its value).
  The goal is admitted too; the report counts the obligation as not checked, neither proved
  nor failed (fix the failure it depends on first).

A proof that refers to *another declaration* whose own proof was admitted — the
postcondition theorem of a function whose `ensures` failed, say — is a proof modulo that
declaration's contract, as every use of a contract is: it counts as proved, the other
declaration's failure is reported, and `sorryAx` shows in the axioms of every item that
depends on it (so none of them is VERIFIED).

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

/-- The tag of a `sorry` (`sorryAx α s tag …`, see `Lean.Meta.mkLabeledSorry`: every `sorry`
Lean elaborates or admits has a unique one); `none` for a `sorry` without a tag. -/
private def sorryTag (e : Expr) : Option Name := do
  guard (e.getAppNumArgs ≥ 3)
  let arg := e.getArg! 2
  if let some t := arg.name? then return t
  guard (arg.isAppOfArity ``Function.const 4)
  arg.appArg!.name?

/-- Add the tags of the `sorry`s in `e` to `acc` (also of a `sorry` inside the type of another). -/
private partial def addSorries (acc : IO.Ref (Array (Option Name))) (e : Expr) : MetaM Unit := do
  unless e.hasSorry do return
  e.forEach' fun s => do
    if s.isAppOf ``sorryAx then
      acc.modify (·.push (sorryTag s))
      for a in s.getAppArgs do addSorries acc a
      return false
    return true

/-- A constant of user code: of the current module, a generated module or a user proof (not of
Lean's or vreact's library, which use no `sorry`). -/
private def isUserConst (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => !([`Init, `Lean, `Std, `Lake, `VReact].contains m.getRoot)
    | none => true

/--
How the proofs of `goals` use `sorry`, through their terms and the constants made while the
obligation ran (auxiliary lemmas, equation lemmas): `none` — not at all; `some true` — only
`sorry`s that were there before it ran (in its goal, or in a constant of user code that existed:
an admitted obligation, a `hole()` or a declaration with an error that the proof unfolded);
`some false` — a `sorry` it made (the automation cheated).

A proof that uses a `sorry` from elsewhere is not a proof of the obligation (it may use the
admitted proof of a false statement to prove a false goal), so it is not counted as proved;
it is not a failure of this obligation either (the obligation may be true): it is *blocked*.
A proof that only refers to another declaration whose proof was admitted (a failed contract
of a function it calls) is a proof modulo that contract, as with every contract; that
declaration's failure is reported, and `sorryAx` shows in the axioms of everything using it.
-/
private partial def sorryUse (old : Environment) (goals : List MVarId) : MetaM (Option Bool) := do
  let used ← IO.mkRef (#[] : Array (Option Name))
  let seen ← IO.mkRef ({} : NameSet)
  let oldConsts ← IO.mkRef (#[] : Array Name)
  -- the proof: its term, and the constants made while it ran (transitively); also the
  -- internal auxiliary lemmas of user code that existed (`_auxLemma`, …: Lean may reuse one
  -- an earlier proof made, which is no contract but a piece of a proof)
  let rec scanNew (e : Expr) : MetaM Unit := do
    addSorries used e
    for c in e.getUsedConstants do
      if (← seen.get).contains c then continue
      seen.modify (·.insert c)
      if old.contains c then
        oldConsts.modify (·.push c)
        unless ((privateToUserName? c).getD c).isInternal && isUserConst old c do continue
      if let some ci := (← getEnv).find? c then
        scanNew ci.type
        if let some v := ci.value? (allowOpaque := true) then scanNew v
  for g in goals do scanNew (← instantiateMVars (mkMVar g))
  let usedTags ← used.get
  if usedTags.isEmpty then return none
  -- the `sorry`s that were there before: in the goal and its hypotheses, and in the constants
  -- of user code the goal or the proof refers to (transitively)
  let before ← IO.mkRef (#[] : Array (Option Name))
  let seenOld ← IO.mkRef ({} : NameSet)
  let rec scanOld (c : Name) : MetaM Unit := do
    if (← seenOld.get).contains c then return
    seenOld.modify (·.insert c)
    unless isUserConst old c do return
    let some ci := old.find? c | return
    for e in [ci.type] ++ (ci.value? (allowOpaque := true)).toList do
      addSorries before e
      for c' in e.getUsedConstants do scanOld c'
  let scanOldIn (e : Expr) : MetaM Unit := do
    addSorries before e
    for c in e.getUsedConstants do scanOld c
  for g in goals do
    g.withContext do
      scanOldIn (← instantiateMVars (← g.getType))
      for d in ← getLCtx do
        scanOldIn (← instantiateMVars d.type)
        if let some v := d.value? then scanOldIn (← instantiateMVars v)
  for c in ← oldConsts.get do scanOld c
  let beforeTags ← before.get
  return some <| usedTags.all fun t => match t with
    | some _ => beforeTags.contains t
    -- a `sorry` without a tag: from elsewhere only if there was one there before
    | none => beforeTags.contains none

/-- The goal, its hypotheses included, mentions `sorryAx` (from a failure above it). -/
private def goalHasSorry (g : MVarId) : MetaM Bool := g.withContext do
  if (← instantiateMVars (← g.getType)).hasSorry then return true
  for d in ← getLCtx do
    if (← instantiateMVars d.type).hasSorry then return true
    if let some v := d.value? then
      if (← instantiateMVars v).hasSorry then return true
  return false

/-- A `sorry` that stands for data (a `hole()`, a declaration with an error), not for a proof:
`sorryAx` at a universe other than `0` (a labeled proof `sorry` is `sorryAx (Name → P)`, a
proposition again). -/
private def isDataSorry (e : Expr) : Bool :=
  e.isAppOf ``sorryAx && match e.getAppFn with
    | .const _ [u] => !u.normalize.isZero
    | _ => true

/-- Whether the goals mention, through reducible definitions of user code (which the
automation unfolds), a `sorry` that stands for data (a `hole()`, a declaration with an error):
a failure on such a goal may be the `sorry`'s, whose value the automation cannot know. (An
admitted *proof* in a definition does not matter: any two proofs of a proposition are equal,
so a failure there is the obligation's own.) -/
private partial def unfoldsToDataSorry (goals : List MVarId) : MetaM Bool := do
  let env ← getEnv
  let seen ← IO.mkRef ({} : NameSet)
  let rec visit (e : Expr) : MetaM Bool := do
    for c in e.getUsedConstants do
      if (← seen.get).contains c then continue
      seen.modify (·.insert c)
      unless isUserConst env c do continue
      let some (.defnInfo d) := env.find? c | continue
      unless (← getReducibilityStatus c) == .reducible do continue
      if (d.value.find? isDataSorry).isSome then return true
      if ← visit d.value then return true
    return false
  goals.anyM fun g => g.withContext do
    if ← visit (← instantiateMVars (← g.getType)) then return true
    for d in ← getLCtx do
      if ← visit (← instantiateMVars d.type) then return true
      if let some v := d.value? then
        if ← visit (← instantiateMVars v) then return true
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
  -- the generated obligations' tactic: on a timeout, `timeoutCases` names the failing case
  let isAuto := match stx[1] with
    | `(tacticSeq| vreact_auto) => true
    | _ => false
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
      match ← sorryUse envBefore goals with
      | none => return none
      | some true => return some { why := m!"its proof uses `sorry` from elsewhere", blocked := true }
      | some false => return some { why := m!"the automation closed the goal with `sorry`" })
    (fun ex => do
      if ex.isMaxHeartbeat then
        let why := m!"(deterministic) timeout: the automation did not finish within this \
          obligation's budget of {budget / 1000} heartbeats (set \"heartbeats\" in vreact.json to change it)"
        -- which case of the goal `vreact_auto` fails on (`timeoutCases`): the goal as stated first
        if isAuto then
          -- (the goal as it was, with the automation's messages so far: `saved` holds the
          -- file's log, which this obligation must not log a second time)
          let log ← Core.getMessageLog
          saved.restore
          Core.setMessageLog log
          if let some cases ← timeoutCases budget then
            return some { why := m!"{why}\n{goalsToMessageData goals}\n{cases}" }
        return some { why }
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
    if f.blocked || sorryBefore || f.why.hasSyntheticSorry || (← unfoldsToDataSorry goals) then
      logWarningAt ref m!"vreact:blocked it depends on `sorry` from elsewhere (an obligation \
        that failed, a declaration with an error, or a hole()) that its goal or its proof \
        contains, so this obligation could not be checked on its own; fix that first\n{f.why}{goal}"
    else
      logWarningAt ref m!"vreact: {f.why}{goal}"
    for g in goals do admitGoal g
    setGoals []

end VReact
