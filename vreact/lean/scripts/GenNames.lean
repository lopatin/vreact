import VReact
/-!
Regenerates `vreact/src/leanNames.ts`, the name lists the translator uses to
escape VTS identifiers (run from `vreact/lean`):

    lake env lean scripts/GenNames.lean

* `LEAN_TOKENS`: identifier-like tokens of the Lean parser in an environment
  importing `VReact` (exactly what generated files see), plus the non-reserved
  keywords (`rec` in `let rec`, …) that do not parse as a name in a position
  where the generated code binds one.  Such an identifier needs escaping.
* `LEAN_ROOT_NAMES`: root components of every constant and alias in that
  environment.  The generated code refers to root names unqualified (`max`,
  `some`, `List`, `Float.ofInt`, …); a user declaration (found first by Lean's
  innermost-namespace resolution) or local with one of these names would
  capture such a reference.
* `LEAN_TYPE_AUX`: names Lean generates inside the namespace of a structure or
  inductive type (`rec`, `casesOn`, `mk`, …).  A field, constructor or enum
  member with one of these names would clash with them.

Only names that are also TypeScript identifiers (`[A-Za-z_$][A-Za-z0-9_$]*`) are kept.
-/
open Lean Lean.Elab

namespace GenNames

def isTsIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    (c.isAlpha || c == '_' || c == '$') && cs.all (fun d => d.isAlphanum || d == '_' || d == '$')

def rootStr (n : Name) : Option String :=
  match n.components.head? with
  | some (.str .anonymous s) => some s
  | _ => none

-- sample declarations shaped like the generated ones (records, enums, unions)
structure S where
  fld : Int
deriving Repr, DecidableEq
inductive E where
  | c1 | c2
deriving Repr, DecidableEq
inductive U where
  | c1 (x : Int) | c2
deriving Repr, DecidableEq

def auxNames (env : Environment) : Array String := Id.run do
  let mut out : Std.HashSet String := {}
  for (n, _) in env.constants.toList do
    match n.components with
    | (.str .anonymous "GenNames") :: (.str .anonymous t) :: (.str .anonymous s) :: _ =>
      if (t == "S" || t == "E" || t == "U") && !["fld", "c1", "c2", "x"].contains s then
        out := out.insert s
    | _ => pure ()
  return out.toArray

/-- The `nonReservedSymbol`s of Lean's parsers (`grep -rhoE 'nonReservedSymbol "[A-Za-z_]+'` over
the toolchain's `src/lean`): identifiers in general, keywords in some positions. -/
def nonReservedCandidates : List String :=
  ["allowTrailingSep", "assert", "axioms", "behavior", "both", "check", "decreasing",
   "default_instance", "dependent", "depth", "ensures", "eq", "eqns", "equations", "erased",
   "expose", "extern", "false", "gen", "generalize", "generalizing", "given", "guard", "imax",
   "induction", "injection", "inline", "intro", "invariant", "is_ground", "is_strict_value",
   "is_value", "kind", "max", "max_insts", "meta", "monotonicity", "motive", "name", "nondep",
   "not_strict_value", "not_value", "postponeValue", "preserveForPP", "priority", "rec",
   "recursor", "requires", "sig", "since", "size", "specialize", "structural", "symbol",
   "tactic", "tags", "true", "usedOnly", "withAnonymousAntiquot", "zeta"]

/-- Positions where generated terms bind a VTS name (parsed and elaborated). -/
def termProbes (c : String) : List String :=
  [s!"let {c} : Int := 1; {c}", s!"fun ({c} : Int) => {c} + 1", s!"fun ((⟨{c}, h⟩ : Int × Int)) => {c}",
   s!"∀ {c} : Int, {c} = {c}", s!"(match (none : Option Int) with | some {c} => {c} | none => 0)",
   s!"let ({c}, y) := ((1 : Int), (2 : Int)); {c} + y"]

/-- Positions in field access / update and declarations (parsed). -/
def parseProbes (c : String) : List (Name × String) :=
  [(`term, s!"x.{c}"), (`term, s!"\{ x with {c} := 1 }"),
   (`command, s!"def {c} (a : Int) : Int := a"), (`command, s!"structure T where\n  {c} : Int"),
   (`command, s!"inductive T where\n  | {c}")]

def elabOk (s : String) : TermElabM Bool := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .error _ => return false
  | .ok stx =>
    let saved ← Core.getMessageLog
    Core.resetMessageLog
    let ok ← try
        let _ ← Term.withoutErrToSorry (Term.elabTerm stx none)
        Term.synthesizeSyntheticMVarsNoPostponing
        pure !(← Core.getMessageLog).hasErrors
      catch _ => pure false
    Core.setMessageLog saved
    return ok

/-- Non-reserved keywords that do not work as names in some generated position (e.g. `let rec`). -/
def badNonReserved : TermElabM (List String) := do
  let env ← getEnv
  nonReservedCandidates.filterM fun c => do
    let elabBad ← (termProbes c).anyM fun s => return !(← elabOk s)
    let parseBad := (parseProbes c).any fun (cat, s) => !(Parser.runParserCategory env cat s).toBool
    return elabBad || parseBad

def render (name : String) (xs : Array String) : String :=
  let sorted := xs.qsort (· < ·)
  let body := ", ".intercalate (sorted.toList.map (fun s => "\"" ++ s ++ "\""))
  s!"export const {name}: readonly string[] = [{body}];\n"

end GenNames
open GenNames

open Lean.Elab in
#eval show Term.TermElabM Unit from do
  let env ← getEnv
  let bad ← badNonReserved
  let mut toks : Array String := (Lean.Parser.getTokenTable env).values.filter isTsIdent
  for c in bad do
    unless toks.contains c do toks := toks.push c
  let mut roots : Std.HashSet String := {}
  for (n, _) in env.constants.toList do
    if let some s := rootStr n then
      unless s == "GenNames" do roots := roots.insert s
  for (n, _) in (Lean.getAliasState env).toList do
    if let some s := rootStr n then roots := roots.insert s
  let rootList := roots.toArray.filter (fun s => isTsIdent s && !toks.contains s)
  let header := "/* Generated by vreact/lean/scripts/GenNames.lean (Lean " ++ Lean.versionString ++
    ", environment `import VReact`). Do not edit. */\n"
  let aux := (auxNames env).filter isTsIdent
  IO.FS.writeFile "../src/leanNames.ts"
    (header ++ render "LEAN_TOKENS" toks ++ render "LEAN_ROOT_NAMES" rootList ++ render "LEAN_TYPE_AUX" aux)
  IO.println s!"{toks.size} tokens (non-reserved: {bad}), {rootList.size} root names, {aux.size} type aux names"
