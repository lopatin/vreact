import Lean
/-!
# `vreact-certify`: the kernel re-check of the built project

`vreact verify` trusts what Lean reports about the generated modules (`vreact:ok` at each
obligation, `#print axioms`) only if every declaration of the project — generated modules and
user proofs — is in the environment *as the kernel checked it*. Lean's elaborator can add a
declaration without the kernel (`set_option debug.skipKernelTC true`, wherever it is set), and
the axiom report cannot show that. So after the build, `vreact` runs this program in a fresh
process: it loads the built modules (`.olean`) and

* replays every declaration of the modules to check into the kernel (`Lean.Kernel.Environment.
  replay`, lean4checker's method): a declaration the kernel rejects (or one of an unsafe or
  `partial` kind, which replay leaves out, used by another) fails its module and every module
  importing it;
* checks what each user proof module (`Proofs.…`) added besides its declarations: entries of
  environment extensions other than the ones theorems, definitions, `@[simp]`/`@[grind]`/
  `@[vreact_simp]` and `grind_pattern` fill (a `macro`, `syntax`, `instance`, `export`, an
  option, … that got past the syntactic whitelist of `ProofCheck.lean`), axioms, declarations in
  the namespaces `VTS`/`VReact`, and declarations that use an axiom other than Lean's standard
  ones, `sorryAx` and the generated `@trusted` axioms (`VReact.assumed`, which the report reads
  as the source's `assume(…)` facts, or one of native evaluation).

Input (stdin, JSON): `{"base": [module…], "check": [module…], "dump": bool}` — `base`: modules
imported as they are (the library, and project modules certified by an earlier run with the
same inputs); `check`: the project modules to re-check, every module before the ones importing
it. Output (stdout, JSON): `{"certified": [module…], "failed": [{"module", "reason"}],
"issues": [{"module", "decl", "msg"}]}` (`decl` may be ""). Exit code 0 unless the program
itself failed (then `vreact` reports the check as not done).
-/
open Lean

namespace VReactCertify

/-- Extensions whose entries a user proof module may have: what theorems, definitions (with
their equation lemmas, matchers, compiled code and documentation), the attributes `simp`,
`vreact_simp`, `grind`, `local`/erased attributes, `grind_pattern`, `namespace`/`section` and
`private`/`protected` names add. Any other extension with entries (instances, syntax,
macros, elaborators, aliases, options, initializers, …) means the module changed more than
lemmas. -/
def allowedExtensions : List String :=
  ["Lean.declRangeExt", "Lean.docStringExt", "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
   "_private.Lean.Namespace.0.Lean.namespacesExt", "Lean.protectedExt", "Lean.noncomputableExt",
   "reducibilityCore", "recExt", "Lean.Compiler.inlineAttrs",
   "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt", "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt",
   "_private.Lean.ExtraModUses.0.Lean.extraModUses", "Lean.deprecatedModuleExt",
   "Lean.Meta.Match.Extension.extension", "Lean.Elab.Structural.eqnInfoExt", "Lean.Elab.WF.eqnInfoExt",
   "Lean.backwardDefeqAttr", "Lean.defeqAttr", "Lean.Meta.simpExtension"]

/-- Extensions by name prefix: the compiler's caches of a definition's code (`Lean.IR.…`,
`Lean.Compiler.LCNF.…`; not `implemented_by`, `extern` or `csimp`, which are elsewhere), grind's
lemma registries (`@[grind …]`, `grind_pattern`), and the simp set `vreact_simp` (registered in
`VReact.Attr` with a hygienic name: the only extension that module declares). -/
def allowedExtension (ext : Name) : Bool :=
  let s := ext.toString (escape := false)
  allowedExtensions.contains s ||
  ["Lean.IR.", "Lean.Compiler.LCNF.", "_private.Lean.IR.", "_private.Lean.Compiler.LCNF.", "Lean.Meta.Grind.",
   "_private.Lean.Meta.Tactic.Grind.", "ext._@.VReact.Attr."].any (s.startsWith ·)

/-- What an extension is about, for the message (by its name). -/
def extensionHint (ext : Name) : String :=
  let s := (ext.toString (escape := false)).toLower
  let has (p : String) := (s.splitOn p).length > 1
  if has "macro" then " (a macro)"
  else if has "parser" || has "token" || has "syntax" || has "notation" then " (syntax)"
  else if has "instance" then " (an instance)"
  else if has "alias" then " (an alias, `export`)"
  else if has "elab" then " (an elaborator)"
  else if has "init" then " (code run at import)"
  else if has "simproc" then " (a simproc)"
  else if has "class" || has "structure" then " (a structure or class)"
  else if has "unif" then " (a unification hint)"
  else if has "coe" then " (a coercion)"
  else if has "implementedby" || has "extern" || has "csimp" then " (compiled code in place of a definition)"
  else if has "meta" then " (meta code)"
  else ""

/-- Lean's standard axioms, `sorryAx` (reported as `sorry`) are allowed in user proofs. -/
def okAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]

structure Out where
  certified : Array Name := #[]
  failed : Array (Name × String) := #[]
  issues : Array (Name × Name × String) := #[]

def issueJson (m d : Name) (msg : String) : Json :=
  Json.mkObj [("module", toString m), ("decl", if d.isAnonymous then "" else toString d), ("msg", msg)]

/-- An axiom of native evaluation: `<decl>._native.<tactic>.ax_…` (`native_decide`, `decide
+native`, `bv_decide`) or `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`. -/
def isNative (d : Name) : Bool :=
  d.components.contains `_native || [`Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler].contains d

/-- What a user proof module added that a proof file may not add (see the module doc). -/
def proofIssues (kenv : Kernel.Environment) (md : ModuleData) : Array (Name × String) := Id.run do
  let mut out : Array (Name × String) := #[]
  for ci in md.constants do
    let n := ci.name
    -- (a theorem there is harmless — Lean realizes equation lemmas such as `VTS.m.f.eq_1` in
    -- the module that first uses them —, a definition could stand in for a generated one)
    if [`VTS, `VReact].contains n.getRoot && !ci.isTheorem then
      out := out.push (n, s!"it declares `{n}` in a namespace of the generated code or of the library")
    match ci with
    | .axiomInfo _ => out := out.push (n, if isNative n then
        s!"it declares `{n}`, an axiom of native evaluation (`native_decide`, `decide +native`, `bv_decide`: it trusts Lean's compiler instead of its kernel)"
        else s!"it declares the axiom `{n}`: an assumption belongs in the source, as `assume(…)` or `@trusted`, where the report shows it")
    | _ => pure ()
    -- the axioms it uses directly (other proof modules' declarations are checked in theirs;
    -- the library and the generated code use none but the standard ones, the generated
    -- `@trusted` axioms and, for the source's `assume(…)` facts, `VReact.assumed`)
    for d in ci.getUsedConstantsAsSet do
      if let some (.axiomInfo _) := kenv.find? d then
        unless okAxioms.contains d || d.getRoot == `VTS do
          out := out.push (n, if d == `VReact.assumed then
            s!"`{n}` uses `VReact.assumed`, the axiom behind the source's `assume(…)` facts: the report would say the result relies on `assume(…)` facts the source does not have"
            else if isNative d then s!"`{n}` uses `{d}`, an axiom of native evaluation (it trusts Lean's compiler instead of its kernel)"
            else s!"`{n}` uses the axiom `{d}`")
  for (ext, es) in md.entries do
    if !es.isEmpty && !allowedExtension ext then
      out := out.push (.anonymous, s!"it adds {es.size} entr{if es.size == 1 then "y" else "ies"} to the environment extension `{ext}`{extensionHint ext}: a proof file may add theorems, definitions and simp/grind attributes, nothing that changes how the generated code is parsed, elaborated or run")
  return out

def run (base check : Array Name) (dump : Bool) : IO Json := do
  let checkSet : NameSet := check.foldl (·.insert ·) {}
  let mut datas : Array (Name × ModuleData) := #[]
  for m in check do
    -- (the compacted regions stay mapped until the process ends)
    let (md, _) ← readModuleData (← findOLean m)
    datas := datas.push (m, md)
  if dump then
    let mut lines : Array Json := #[]
    for (m, md) in datas do
      let exts := md.entries.filter (!·.2.isEmpty) |>.map fun (e, es) => Json.mkObj [("ext", toString e), ("n", es.size)]
      lines := lines.push (Json.mkObj [("module", toString m), ("exts", Json.arr exts)])
    return Json.arr lines
  let mut imports : Array Name := base
  for (_, md) in datas do
    for i in md.imports do
      if !checkSet.contains i.module && !imports.contains i.module then imports := imports.push i.module
  let env ← importModules (imports.map ({ module := · })) {} (loadExts := false)
  let mut kenv := env.toKernelEnv
  let mut out : Out := {}
  -- the failed modules, each with the reason at the root of its failure
  let mut failed : NameMap String := {}
  for (m, md) in datas do
    if let some i := md.imports.find? (fun i => failed.contains i.module) then
      let root := failed.getD i.module ""
      failed := failed.insert m root
      out := { out with failed := out.failed.push (m, s!"it imports {i.module}, which failed the check: {root}") }
      continue
    let mut consts : Std.HashMap Name ConstantInfo := {}
    for ci in md.constants do consts := consts.insert ci.name ci
    match ← (kenv.replay consts).toBaseIO with
    | .error e =>
      let msg := (toString e).trimAscii.toString
      -- (`replay` names the declaration: "while replaying declaration 'X':\n…")
      let decl := match (msg.splitOn "while replaying declaration '").getD 1 "" |>.splitOn "'" with
        | d :: _ => d.toName
        | [] => .anonymous
      let why := s!"Lean's kernel rejects {if decl.isAnonymous then "a declaration" else s!"`{decl}`"} of {m} when it is checked again (it was added without the kernel's check, e.g. with `debug.skipKernelTC`)"
      failed := failed.insert m why
      out := { out with failed := out.failed.push (m, why), issues := out.issues.push (m, decl, s!"the kernel rejects it when it is checked again (it was added without the kernel's check, e.g. with `debug.skipKernelTC`): {msg}") }
      continue
    | .ok k => kenv := k
    if m.getRoot == `Proofs then
      let is := proofIssues kenv md
      if let some (_, first) := is[0]? then
        let why := s!"the user proof {m} does more than state lemmas: {first}"
        failed := failed.insert m why
        out := { out with failed := out.failed.push (m, why), issues := out.issues ++ is.map fun (d, msg) => (m, d, msg) }
        continue
    out := { out with certified := out.certified.push m }
  return Json.mkObj [
    ("certified", Json.arr (out.certified.map (toJson ·.toString))),
    ("failed", Json.arr (out.failed.map fun (m, r) => Json.mkObj [("module", toString m), ("reason", r)])),
    ("issues", Json.arr (out.issues.map fun (m, d, msg) => issueJson m d msg))]

end VReactCertify

open VReactCertify in
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let input ← (← IO.getStdin).readToEnd
  let j ← IO.ofExcept (Json.parse input)
  let names (k : String) : IO (Array Name) := do
    let a ← IO.ofExcept (j.getObjValAs? (Array String) k)
    return a.map (·.toName)
  let dump := (j.getObjValAs? Bool "dump").toOption.getD false
  IO.println (← run (← names "base") (← names "check") dump).compress
  return 0
