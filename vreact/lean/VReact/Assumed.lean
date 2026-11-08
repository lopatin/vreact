import Lean
import VReact.Core
/-!
# `assume(c)`: what is assumed, and who may assume it

`VReact.assumed {p : Prop} : p` (Core.lean) is the axiom behind `assume(c)`, and `vreact verify`
reports an item whose `#print axioms` lists it as ASSUMES — "relies on the program's
`assume(…)` facts". The axiom proves anything, so that report is honest only if (1) what each
`assume(c)` contributes is exactly the fact the program's reviewer vouches for, and (2) every
use of the axiom in the item's dependency cone comes from an `assume(…)` of the program.

## (1) `vreact_assume`: the fact under its path

The translator writes `have h : c := (by vreact_assume)` where the program says `assume(c)`.
Lean keeps every nested proof of a definition as an auxiliary theorem of its own
(`f._proof_N`, a constant user proofs can name) closed over the variables the proof mentions.
`VReact.assumed` at `c` alone would mention only the variables of `c`, so the theorem would be
`∀ xs i, 0 ≤ i ∧ i < xs.length` for an `assume` that the program reaches only under
`if (flag)` and the function's `requires` — a stronger statement than the program's, false
even when the `assume` is (`if (flag) assume(flag)` would become `∀ flag, flag = true`).
`vreact_assume` assumes `c` under every hypothesis in scope — the function's precondition
`h_pre`, the conditions of the `if`/`match` branches leading to it, a callback's membership
facts, … (the local proofs without a value; proved `have`s follow from them) — and applies
the result to them: the auxiliary theorem is `∀ args, h_pre → path → c`, the fact as the
program states it: `c` holds whenever control reaches the `assume`, for every input the
function's contracts allow. The translator rejects `assume` where the context is more general
than the program's: in a generic function (the theorem would also be `∀ {T : Type}`, for types
JS never passes), a `for…of` body (any accumulator and element), an array-method callback (any
element) and a functional update (any state).

## (2) `#vreact_assumed X`: uses that are not the program's

A user proof that uses the axiom itself (`theorem t : (1 : Int) = 2 := VReact.assumed`, or
through a renaming `open`, an auxiliary definition, a tactic, a term built by metaprogramming,
…) states an unproved fact of its own: it is an axiom declared in a user proof, whatever its
keyword. `#vreact_assumed X` lists the declarations in the dependency cone of `X` (through types
and values, as `#print axioms` follows them) whose own type or value mentions `VReact.assumed`
and that are not generated: they come from an imported module outside `VTS.*` (a user proof
`Proofs.*`; the VReact library mentions the axiom nowhere else, AssumedTest.lean checks that).
Declarations of the current file are generated, since the generator writes this command only
at the end of its own files. It reads the kernel's environment, as `#print axioms` does, and
always prints (the report needs it as evidence whenever the axioms of `X` include
`VReact.assumed`):

    'X' uses VReact.assumed outside the generated code: [a, b]

`vreact verify` then reports `X`'s item TRUSTED, naming `a` and `b`, as for an axiom a user
proof declares. (Modules of Lean itself — `Init`, `Lean`, `Std`, `Lake` — do not import VReact
and are not searched.)
-/
namespace VReact
open Lean Elab Meta Tactic Command

/-- `assume(c)`'s proof (see the module doc): `VReact.assumed` at `∀ hyps, c`, applied to the
hypotheses in scope (the local proofs without a value, in context order). -/
elab "vreact_assume" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let mut hs : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let .cdecl .. := d then
      if ← isProp d.type then hs := hs.push d.toExpr
  let fact ← mkForallFVars hs tgt
  g.assign (mkAppN (mkApp (mkConst ``VReact.assumed) fact) hs)

/-- Modules that do not import VReact (Lean's own): nothing in them can mention `VReact.assumed`. -/
private def leanOwnModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Init || r == `Lean || r == `Std || r == `Lake

/-- The worklist of `assumedOutsideGenerated` (each constant is visited once). -/
private partial def assumedGo (env : Environment) (kenv : Kernel.Environment) :
    List Name → NameSet → Array Name → Array Name
  | [], _, found => found
  | c :: todo, seen, found =>
    if seen.contains c then assumedGo env kenv todo seen found else
    let seen := seen.insert c
    let mod := (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
    if mod.any leanOwnModule then assumedGo env kenv todo seen found else
    match kenv.find? c with
    | none => assumedGo env kenv todo seen found
    | some ci =>
      let used := ci.getUsedConstantsAsSet
      -- (no module: the current file, which is generated)
      let generated := mod.all fun m => m.getRoot == `VTS
      let found := if !generated && c != ``VReact.assumed && used.contains ``VReact.assumed then found.push c else found
      assumedGo env kenv (used.foldl (fun acc u => if seen.contains u then acc else u :: acc) todo) seen found

/--
The declarations in the dependency cone of `root` (types, values, constructors) that are not
generated and whose own type or value mentions `VReact.assumed` (see the module doc).
-/
def assumedOutsideGenerated (env : Environment) (root : Name) : Array Name :=
  (assumedGo env env.toKernelEnv [root] {} #[]).qsort Name.lt

elab "#vreact_assumed " id:ident : command => do
  -- (no message for a name that does not resolve: its `#print axioms` fails too, and an item
  -- without both reports is not counted as checked)
  let cs ← try liftCoreM <| realizeGlobalConstWithInfos id catch _ => pure []
  for c in cs do
    let found := assumedOutsideGenerated (← getEnv) c
    logInfo m!"'{c}' uses VReact.assumed outside the generated code: {found.toList}"

end VReact
