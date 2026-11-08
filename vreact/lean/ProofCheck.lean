import Lean
/-!
# `vreact-proofcheck`: the whitelist for user proof files

User proofs (`proofs/**/*.lean`, copied to `Proofs/` of the generated project) are imported
by the generated Lean files. Lean elaborates them *before* the generated code that imports
them, so anything they declare runs, or takes effect, while the translation is checked: a
`macro`, `syntax` or `macro_rules` changes how the generated code and vreact's tactics parse;
an `instance` changes which `==`, `DecidableEq` or string conversion the generated code uses;
`set_option debug.skipKernelTC true` lets declarations into the environment that the kernel
never checked; `#eval`, `run_tac`, `initialize`, … run arbitrary code (they can rewrite the
generated files or the report). The axiom report catches `sorry` and new axioms, none of
these.

So, before Lean runs, `vreact` hands every proof file to this program, which **parses** it
with Lean's own parser, in exactly the environment the file will be elaborated in (`envFor`:
`Init` + `VReact` when its imports reach `VReact` or a generated module, also through the proof
files it imports; `Init` alone otherwise; scope commands `open`/`namespace`/`section`/`end` are
elaborated, so scoped syntax is parsed as Lean will parse it), and accepts only:

* the header: plain `import`s of `VTS.*` (generated modules), `Proofs.*` (other proof files:
  existing ones, without a cycle), `VReact` and `Init` — not a part of the library or of `Init`
  (`VReact.JS`, `Init.Core`), whose syntax differs from both environments;
* `theorem`, `def`, `abbrev`, `example` (modifiers: doc comment, the attributes below,
  `private`, `protected`, `noncomputable`, `nonrec`), named outside the namespaces `VTS` and
  `VReact` (the generated declarations and the library) and not named like a `VReact.` name
  (generated files `open VReact`);
* `open`, `namespace`/`section`/`end` (no namespace under `VTS` or `VReact`; `section` or
  `noncomputable section`, no module-system modifiers), `variable`, `universe`, `include`,
  `omit`, module docs `/-! … -/`, `#check`, `#print`; `open … in` and `set_option … in`
  before any of these but `namespace`/`section`/`end` (which `in` would leave open unseen);
  no `_root_.VTS…`/`_root_.VReact…` name anywhere (`where`/`let rec` declare with it);
* attributes `simp`, `vreact_simp`, `grind` (and `grind!`, `grind?`, `grind!?`), also `local`
  and, in `attribute [-…]`, erased; `grind_pattern`;
* `set_option` of `maxHeartbeats`, `maxRecDepth`, `synthInstance.maxHeartbeats`,
  `synthInstance.maxSize`, `autoImplicit`, `relaxedAutoImplicit`, `diagnostics`,
  `diagnostics.threshold`, the registered `linter.*` and `pp.*` options with a Bool or Nat
  value, and `trace.C` for a registered trace class `C` — not `trace.profiler` and its
  options, which write files or start a web server and a browser (as a command, `… in`, inside
  terms and tactics, and in any other syntax with the keyword `set_option`, e.g. grind's
  interactive `set_option … in`: `setsOption`);
* inside terms and tactics anything except code execution and trusted evaluation:
  `run_tac`, `by_elab`, `unsafe`, `include_str`, `native_decide`, `+native`, a `decide
  (config := …)` value (it can be `+native`), the `bv_decide` tactics (also of `grind =>` and
  `sym =>`), `idbg`, `dbg_trace` and the `dbgTrace…` functions (output), the library's test
  tactics, the `Lean.ofReduceBool` family, and the identifier `assumed` (`VReact.assumed`, the
  axiom of the source's `assume(…)` facts, in any spelling);
* string, character and name literals and names without line breaks or other control
  characters (Lean prints them in its messages, where such a line could read like a message
  about another file).

This check is what stops code from running while Lean elaborates a proof file; after the build,
`vreact-certify` (`Certify.lean`) re-checks every declaration with the kernel and what each
proof module added, independently of how it was written.

Usage: the files arrive on stdin as a JSON array `[{"name": …, "text": …}]` (`name`, the path
relative to the proofs directory, names the module, `sub/x.lean` is `Proofs.sub.x`, and is used in
the messages); the result is a JSON array `[{"file", "line", "col", "msg"}]` on stdout (lines
1-based, columns 1-based), empty when every file is acceptable. Exit code 0 unless the
program itself failed.
-/
open Lean Elab Command Parser

namespace VReactProofCheck

/-- Options a proof file may set by their exact names: resource limits and diagnostics. -/
def exactOptions : List Name :=
  [`maxHeartbeats, `maxRecDepth, `synthInstance.maxHeartbeats, `synthInstance.maxSize,
   `autoImplicit, `relaxedAutoImplicit, `diagnostics, `diagnostics.threshold]

/-- The description `registerTraceClass` gives the option `trace.C` of a trace class `C`. -/
def traceClassDescr : String := "enable/disable tracing for the given module and submodules"

/-- Options a proof file may set: resource limits and output, nothing that changes what is
checked or how, and nothing that does more than print messages. Besides `exactOptions`: the
switch `trace.C` of a registered trace class `C` (not `trace.profiler` and its options: they
write files — `trace.profiler.output` — or start a web server and a browser —
`trace.profiler.serve`), and registered `pp.*` / `linter.*` options with a Bool or Nat value. -/
def optionAllowed (n : Name) : IO Bool := do
  if exactOptions.contains n then return true
  let some d := (← getOptionDecls).find? n | return false
  let boolOrNat := match d.defValue with | .ofBool _ | .ofNat _ => true | _ => false
  match n.getRoot with
  | `trace =>
    -- (two trace switches Lean registers as options of their own)
    return !(`trace.profiler).isPrefixOf n && d.defValue == .ofBool false &&
      (d.descr == traceClassDescr || [`trace.Meta.synthInstance, `trace.Meta.isDefEq.printTransparency].contains n)
  | `pp | `linter => return boolOrNat
  | _ => return false

private def attrName (s : String) : Name := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Lean") "Parser") "Attr") s

/-- Attribute syntax kinds a proof file may use: the simp sets and `grind`. -/
def attrKindsAllowed : List Name :=
  [attrName "simp", attrName "grind", attrName "grind!", attrName "grind?", attrName "grind!?",
   Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Parser") "Attr") "vreact_simp"]

/-- Attribute names `attribute [-…]` may erase. -/
def erasableAttrs : List Name := [`simp, `vreact_simp, `grind]

def reservedRoots : List Name := [`VTS, `VReact]

/-- The imports a proof file may have: the generated modules, other proof files, the whole
library and `Init`. A *part* of the library or of `Init` (`VReact.JS`, `Init.Core`) is not
allowed: a file is parsed in the environment of its imports (see `envFor`), which is `Init`
or `Init` + `VReact` only with these imports (a file importing `VReact.JS` alone has neither
`Init`'s nor `VReact`'s syntax: e.g. `m!` is a token in `VReact`, an identifier in `Init.Core`). -/
def allowedImport (m : Name) : Bool :=
  m == `VReact || m == `Init || [`VTS, `Proofs].contains m.getRoot && !m.isAtomic

/-- Constants whose use trusts compiled code instead of the kernel. -/
def trustedEval : List String := ["ofReduceBool", "ofReduceNat", "reduceBool", "reduceNat", "trustCompiler"]

structure Issue where
  pos : String.Pos.Raw
  msg : String

abbrev M := StateT (Array Issue) CommandElabM

/-- Where `stx` starts, after a leading doc comment (and, for a declaration, after its
modifiers): the position a message about a command points at. -/
partial def startPos? (stx : Syntax) : Option String.Pos.Raw :=
  match stx with
  | .node _ k args =>
    if k == ``Command.docComment || k == ``Command.declModifiers then none
    else args.findSome? startPos?
  | _ => stx.getPos?

def report (stx : Syntax) (msg : String) : M Unit := do
  let pos := (startPos? stx).getD (stx.getPos?.getD 0)
  modify (·.push { pos, msg })

/-- The source text of `stx` (from `startPos?`), first line, shortened. -/
def excerpt (stx : Syntax) : CommandElabM String := do
  let fm ← getFileMap
  let some s := startPos? stx <|> stx.getPos? | return ""
  let some e := stx.getTailPos? | return ""
  let txt := (String.Pos.Raw.extract fm.source s e)
  let line := (txt.splitOn "\n").headD ""
  return if line.length > 60 then (line.take 57).toString ++ "…" else line

def whitelistHint : String :=
  "a proof file may contain only theorem/def/abbrev/example, open, namespace/section/end, variable, " ++
  "universe, include/omit, #check/#print, attribute [simp|vreact_simp|grind …], grind_pattern and " ++
  "set_option of maxHeartbeats/maxRecDepth/synthInstance.*/linter.*/pp.*/trace.<trace class> " ++
  "(see reference/obligations.md, \"Lean lemmas\")"

def optionMsg (n : Name) : String :=
  s!"`set_option {n}` is not allowed in a proof file: only resource limits and output options " ++
  "(maxHeartbeats, maxRecDepth, synthInstance.maxHeartbeats/maxSize, autoImplicit, diagnostics, the linter.* and pp.* options, " ++
  "and trace.C for a trace class C) may be set; other options can change what Lean checks (e.g. debug.skipKernelTC skips the kernel) " ++
  "or do more than print messages (trace.profiler.output writes a file, trace.profiler.serve starts a web server and a browser)"

/-- The message for a command (or declaration) kind that is not whitelisted. -/
def commandMsg (k : Name) (text : String) : String :=
  let s := k.toString
  let has (p : String) := (s.splitOn p).length > 1
  let why :=
    if [``Command.axiom].contains k then
      "an axiom is an unproved assumption: state it as a theorem and prove it (assumptions belong in the source, as `assume(…)` or `@trusted`, where the report shows them)"
    else if [``Command.instance].contains k || has "deriving" || has "Deriving" then
      "an instance can change the meaning of the generated code (which `==`, `DecidableEq` or string conversion it uses); state the facts you need as theorems"
    else if has "macro" || has "syntax" || has "notation" || has "infix" || has "prefix" || has "postfix" ||
        has "elab" || has "mixfix" || has "binder_predicate" || has "binderPredicate" || has "unif_hint" || has "unifHint" ||
        has "declare" || has "Declare" || has "Config" then
      "syntax extensions (macro, macro_rules, syntax, notation, elab, …) change how the generated code and vreact's tactics parse and run; help the automation with lemmas tagged @[vreact_simp], @[simp] or @[grind …], or with grind_pattern"
    else if has "eval" || has "Eval" || has "run" || has "initialize" || has "Initialize" || has "exit" then
      "running code while the proofs are checked can change the environment, the generated files or the report"
    else if has "simproc" || has "Simproc" || has "dsimproc" || has "propagator" then
      "simprocs and grind propagators run code inside the automation; state rewrite rules as theorems tagged @[vreact_simp] or @[simp]"
    else if [``Command.opaque, ``Command.structure, ``Command.inductive, ``Command.classInductive].contains k ||
        has "coinductive" || has "mutual" then
      "only theorem, def, abbrev and example declarations are allowed"
    else if has "export" then
      "`export` adds aliases that can change what a name in the generated code refers to"
    else
      "it is not on the whitelist"
  s!"`{text}` is not allowed in a proof file: {why}; {whitelistHint}"

def bannedKind? (k : Name) : Option String :=
  let s := k.toString
  if k == ``Lean.Parser.Tactic.runTac then some "`run_tac` runs arbitrary code"
  else if k == `Lean.byElab then some "`by_elab` runs arbitrary code"
  else if k == ``Lean.Parser.Term.unsafe then some "`unsafe` terms run compiled code that the kernel does not check"
  else if k == ``Lean.Parser.Term.elabToSyntax then some "this term is internal to Lean's elaborator"
  else if k == `Lean.includeStr then some "`include_str` reads files"
  else if k == ``Lean.Parser.Term.idbg then some "`idbg` runs code"
  else if k == ``Lean.Parser.Tactic.nativeDecide then some "`native_decide` trusts compiled code instead of the kernel (it adds an axiom `…._native.…`)"
  else if (match k with | .str _ last => ["bvDecide", "bvCheck", "bvTrace", "bvDecidePush", "nativeDecide"].contains last | _ => false) then
    -- (also the `grind => …` / `sym =>` forms, `Lean.Parser.Tactic.Grind.bvDecide`, …)
    some "the bv_decide tactics run an external SAT solver and trust compiled code instead of the kernel (an axiom `…._native.…`)"
  else if (s.splitOn "vreact_test").length > 1 || (s.splitOn "Vreact_test").length > 1 || (s.splitOn "Server.Test").length > 1 then
    some "the library's test tactics are not for proofs"
  else if (s.splitOn "dbg").length > 1 || (s.splitOn "Dbg").length > 1 then
    -- (`dbg_trace` as a tactic, a term and a `do` element)
    some "`dbg_trace` prints to Lean's output while the proofs are checked"
  else none

/-- Identifiers a proof file may not use (by their last component, so also qualified, with
`_root_`, `@`, `«…»`, in `open … (…)`/`renaming`, `attribute […]`). -/
def bannedIdent? (n : Name) : Option String :=
  match n with
  | .str _ last =>
    if last == "assumed" then
      some "`VReact.assumed` is the axiom behind the source's `assume(…)` facts: a proof that uses it proves anything, and the report would say the result relies on `assume(…)` facts that the source does not have; prove the lemma instead (an assumption belongs in the source, as `assume(…)` or `@trusted`, where the report shows it); a local name `assumed` must be renamed"
    else if ["dbgTrace", "dbgTraceIfShared", "dbgTraceVal", "dbgSleep", "dbgStackTrace", "dbgStackTraceIf",
        "dbgShowTokens", "dbgTraceStateFn", "dbgToString", "dbgFormatAsyncState", "dbgFormatCheckedSyncState"].contains last then
      some s!"`{last}` is one of Lean's debugging functions (it prints to Lean's output or waits while the proofs are checked)"
    else none
  | _ => none

def bannedAtom? (a : String) : Option String :=
  if a == "unsafe" then some "`unsafe` code is not checked by the kernel"
  else if a == "partial" then some "`partial` definitions are not allowed (state the function with structural or well-founded recursion)"
  else if a == "native_decide" then some "`native_decide` trusts compiled code instead of the kernel (it adds an axiom `…._native.…`)"
  else if a == "run_tac" || a == "by_elab" then some s!"`{a}` runs arbitrary code"
  else if a == "deriving" || a == "instance" then some "an instance can change the meaning of the generated code (which `==`, `DecidableEq` or string conversion it uses)"
  else none

/-- Whether `stx` contains the atom `a`. -/
partial def hasAtom (stx : Syntax) (a : String) : Bool :=
  match stx with
  | .atom _ v => v == a
  | .node _ _ args => args.any (hasAtom · a)
  | _ => false

/-- The atoms of `stx`. -/
partial def atomsOf (stx : Syntax) : Array String :=
  match stx with
  | .atom _ v => #[v]
  | .node _ _ args => args.flatMap atomsOf
  | _ => #[]

/-- Whether `stx` is a syntax node that sets an option: it has the keyword `set_option` as one
of its own tokens (a command, `… in` as a term or a tactic, grind's interactive `set_option …
in` — `Lean.Parser.Tactic.Grind.setOption` —, and any other mode's), or its kind is named
like an option setter. -/
def setsOption (stx : Syntax) : Bool :=
  match stx with
  | .node _ k args =>
    let s := k.toString
    let has (p : String) := (s.splitOn p).length > 1
    args.any (fun a => match a with | .atom _ v => v.trimAscii == "set_option" | _ => false) ||
      has "set_option" || has "setOption" || has "SetOption" || has "withOption" || has "with_option"
  | _ => false

/-- Check a node that sets an option (`setsOption`): the option is named by its first
identifier (child 1 in every such syntax of Lean 4.35, which the elaborators read with
`stx[1].getId`); one without an identifier there is not understood, so it is rejected. -/
def checkSetOption (stx : Syntax) : M Unit := do
  let id := stx[1]
  if !id.isIdent || (stx.getArgs.findIdx? (·.isIdent)) != some 1 then
    report stx s!"`{← excerpt stx}` is not allowed in a proof file: an option can only be set with `set_option <name> <value>`"
    return
  let n := id.getId
  unless ← optionAllowed n do report stx (optionMsg n)

/-- Characters that may not occur in a literal or a name of a proof file: line breaks (and the
other control characters). Lake prints Lean's messages as text, one message starting a line
`info: <file>:<line>:<col>: …`; a message with a line break in it (`#print "…"`, the `fail`,
`trace` and `dbg_trace` tactics, a name `«…»` in an error) could print a line that reads like a
message of another file — e.g. `vreact:ok` at an obligation of a generated file. -/
def badChar (c : Char) : Bool :=
  (c.toNat < 0x20 && c != '\t') || c.toNat == 0x7f || c.toNat == 0x85 || c.toNat == 0x2028 || c.toNat == 0x2029

def lineBreakMsg (what : String) : String :=
  s!"{what} with a line break (or another control character) is not allowed in a proof file: Lean prints it in its " ++
  "messages, where it could start a line that reads like a message about another file (e.g. a generated one); write it on one line"

/-- `decide (config := c)`: the configuration value may switch on native evaluation
(`DecideConfig.native`: `⟨false, true, true, false⟩` is `+native`). -/
partial def configValueItem? (stx : Syntax) : Option Syntax :=
  match stx with
  | .node _ k args =>
    if k == ``Lean.Parser.Tactic.valConfigItem && (args.findSome? fun a => if a.isIdent then some a.getId else none) == some `config then some stx
    else args.findSome? configValueItem?
  | _ => none

/-- Every node of `stx`: banned kinds/atoms, attributes, options. -/
partial def walk (stx : Syntax) : M Unit := do
  match stx with
  | .node _ k args =>
    if let some why := bannedKind? k then
      report stx s!"`{← excerpt stx}` is not allowed in a proof file: {why}"
      return
    if setsOption stx then
      checkSetOption stx
    if k == ``Lean.Parser.Term.attrInstance then
      -- attrKind (scoped/local), then the attribute itself
      if hasAtom stx[0] "scoped" then
        report stx s!"`{← excerpt stx}`: scoped attributes are not allowed in a proof file (use the attribute itself, or `local`)"
      let a := stx[1]
      unless attrKindsAllowed.contains a.getKind do
        report a s!"the attribute `{← excerpt a}` is not allowed in a proof file: only simp, vreact_simp and grind (grind =, grind →, …) are; other attributes can change how the generated code is elaborated or compiled (instance, coe, macro, implemented_by, extern, reducible, …)"
        return
    if k == ``Lean.Parser.Command.eraseAttr then
      unless erasableAttrs.contains stx[1].getId do
        report stx s!"`{← excerpt stx}` is not allowed in a proof file: only simp, vreact_simp and grind attributes may be erased"
    if k == ``Lean.Parser.Tactic.decide then
      if let some item := configValueItem? stx then
        report item s!"`{← excerpt item}` is not allowed in a proof file: a configuration value can switch on native evaluation (`⟨false, true, true, false⟩` is `+native`), which trusts compiled code instead of the kernel; write the options as `+kernel`, `+revert`, `-zetaReduce`"
    -- literals: no line breaks (see `badChar`)
    if k == strLitKind || k == charLitKind || k == nameLitKind || k == interpolatedStrLitKind then
      let raw := (atomsOf stx).foldl (· ++ ·) ""
      let decoded : Option String :=
        if k == strLitKind then stx.isStrLit?
        else if k == charLitKind then stx.isCharLit?.map toString
        else if k == nameLitKind then stx.isNameLit?.map fun n => ".".intercalate (n.components.map (·.toString (escape := false)))
        else stx.isInterpolatedStrLit?
      if raw.any badChar || (decoded.map (·.any badChar)).getD true then
        report stx (lineBreakMsg "a string, character or name literal")
      return
    for a in args do walk a
  | .atom _ v =>
    if let some why := bannedAtom? v then
      report stx s!"`{v}` is not allowed in a proof file: {why}"
  | .ident _ raw n _ =>
    if raw.toString.any badChar || n.components.any (fun c => (c.toString (escape := false)).any badChar) then
      report stx (lineBreakMsg "a name")
    if let some why := bannedIdent? n then
      report stx s!"`{n}` is not allowed in a proof file: {why}"
    if let .str _ last := n then
      if trustedEval.contains last then
        report stx s!"`{n}` is not allowed in a proof file: it trusts compiled code instead of the kernel"
      if n == `native then
        report stx "`native` (e.g. `decide +native`) is not allowed in a proof file: it trusts compiled code instead of the kernel (it adds an axiom `…._native.…`)"
    -- (`where`/`let rec` names with `_root_` declare at the root: `_root_.VTS.m.f` would be
    -- a generated name; references never need `_root_` for these namespaces)
    if n.getRoot == `_root_ && reservedRoots.contains (n.replacePrefix `_root_ .anonymous).getRoot then
      report stx s!"`{n}` is not allowed in a proof file: the namespaces VTS and VReact belong to the generated code and the library (refer to their names without `_root_`)"
  | .missing => pure ()

/-- The full name a declaration id declares in the current namespace. -/
def fullName (id : Name) : CommandElabM Name := do
  if id.getRoot == `_root_ then return id.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ id

def checkDeclName (declId : Syntax) : M Unit := do
  let id := declId[0].getId
  let n ← fullName id
  if reservedRoots.contains n.getRoot then
    report declId s!"`{n}` is not allowed in a proof file: the namespaces VTS and VReact belong to the generated code and the library (a declaration there can replace or extend a translated declaration); name it outside them"
  else if (← getEnv).contains (`VReact ++ n) then
    report declId s!"`{n}` is not allowed in a proof file: the generated code opens VReact, where `VReact.{n}` exists, so the name would become ambiguous there; choose another name"

/-- Commands the check elaborates after accepting them, so that the parser state stays Lean's:
namespaces and `open` activate scoped syntax; options (whitelisted ones only) are in the
parser's context. -/
def scopeKinds : List Name :=
  [``Command.open, ``Command.namespace, ``Command.section, ``Command.end, ``Command.set_option]

def plainKinds : List Name :=
  [``Command.open, ``Command.namespace, ``Command.section, ``Command.end, ``Command.variable,
   ``Command.universe, ``Command.include, ``Command.omit, ``Command.check, ``Command.print,
   ``Command.printAxioms, ``Command.moduleDoc, ``Command.attribute, ``Command.set_option,
   ``Command.grindPattern]

partial def checkCommand (stx : Syntax) : M Unit := do
  let k := stx.getKind
  if k == ``Command.declaration then
    let mods := stx[0]
    let decl := stx[1]
    let dk := decl.getKind
    if [``Command.theorem, ``Command.definition, ``Command.abbrev].contains dk then
      checkDeclName decl[1]
    else if dk != ``Command.example then
      report stx (commandMsg dk (← excerpt stx))
      return
    -- modifiers: no `meta` (the rest is checked by `walk`: unsafe, partial, attributes)
    if hasAtom mods "meta" then report mods s!"`meta` declarations are not allowed in a proof file"
    walk stx
  else if k == ``Command.in then
    let c1 := stx[0]
    unless [``Command.open, ``Command.set_option].contains c1.getKind do
      report stx s!"`{← excerpt stx}` is not allowed in a proof file: only `open … in` and `set_option … in` are"
      return
    -- `c₁ in c₂` is `section c₁ c₂ end`: a scope command as c₂ would leave a namespace open
    -- (its `end` fails) that this check, which does not elaborate `in`, would not see
    if [``Command.namespace, ``Command.section, ``Command.end].contains stx[2].getKind then
      report stx s!"`{← excerpt stx}` is not allowed in a proof file: `… in` may precede a declaration or command, not `namespace`, `section` or `end`"
      return
    checkCommand c1
    checkCommand stx[2]
  else if k == ``Command.section && (atomsOf stx[0]).any (· != "noncomputable") then
    -- `meta section`, `public section`, `@[expose] section`: module-system modifiers
    report stx s!"`{← excerpt stx}` is not allowed in a proof file: only `section` and `noncomputable section` are"
  else if plainKinds.contains k then
    walk stx
  else
    report stx (commandMsg k (← excerpt stx))

/-- The environment a file is parsed in: exactly the syntax its imports give Lean (the token
table and the parsers). Its imports are `Init`, `VReact`, generated modules (`VTS.…`, which
import `VReact`) and other proof files (`Proofs.…`); generated modules and proof files add no
syntax (the latter are checked too, in the environment of *their* imports), and `VReact`'s
imports contain `Init`. So the environment is `Init` + `VReact` when the file's imports reach
`VReact` or a generated module (directly or through the proof files it imports: `withLib`),
and `Init` alone otherwise. -/
def envFor (withLib : Bool) (cache : IO.Ref (Option Environment × Option Environment))
    (enableInit : IO Unit) : IO Environment := do
  let (init?, vr?) ← cache.get
  if !withLib then
    if let some e := init? then return e
    enableInit
    let e ← importModules #[{ module := `Init }] {} (loadExts := true)
    cache.set (some e, vr?)
    return e
  else
    if let some e := vr? then return e
    enableInit
    let e ← importModules #[{ module := `Init }, { module := `VReact }] {} (loadExts := true)
    cache.set (init?, some e)
    return e

def posOf (fm : FileMap) (p : String.Pos.Raw) : Nat × Nat :=
  let q := fm.toPosition p
  (q.line, q.column + 1)

/-- The module a proof file is (`sub/x.lean` is `Proofs.sub.x`, as `vreact` names it). -/
def moduleOfFile (name : String) : Name :=
  ("Proofs." ++ ((name.dropEnd 5).toString.replace "/" ".")).toName

/-- The imports of a proof file's header, with their positions (none if it does not parse). -/
def headerImports (name text : String) : IO (Array (Name × String.Pos.Raw)) := do
  let inputCtx := Parser.mkInputContext text name
  let (header, _, msgs) ← Parser.parseHeader inputCtx
  if msgs.hasErrors then return #[]
  return header.raw[2].getArgs.map fun imp => (imp[4].getId, imp.getPos?.getD 0)

/-- Whether a proof module's imports reach `VReact` (directly, through a generated module or
through the proof files it imports), and the problems of its own imports of proof files: one
that does not exist, or a cycle (Lean rejects both; the check reports them before Lean runs). -/
partial def reachesLib (imports : Std.HashMap Name (Array (Name × String.Pos.Raw))) (m : Name)
    (visiting : List Name := []) : Bool :=
  (imports.getD m #[]).any fun (i, _) =>
    i == `VReact || i.getRoot == `VTS ||
      (i.getRoot == `Proofs && !visiting.contains i && imports.contains i && reachesLib imports i (m :: visiting))

/-- Whether proof module `m` is on an import cycle (through `i`, one of its imports). -/
partial def onCycle (imports : Std.HashMap Name (Array (Name × String.Pos.Raw))) (m i : Name)
    (seen : List Name := []) : Bool :=
  i == m || (!seen.contains i && (imports.getD i #[]).any fun (j, _) => onCycle imports m j (i :: seen))

def checkFile (name text : String) (withLib : Bool) (proofMods : Std.HashMap Name (Array (Name × String.Pos.Raw)))
    (cache : IO.Ref (Option Environment × Option Environment))
    (enableInit : IO Unit) : IO (Array (Nat × Nat × String)) := do
  let inputCtx := Parser.mkInputContext text name
  let fm := inputCtx.fileMap
  let (header, pstate, msgs) ← Parser.parseHeader inputCtx
  let mut out : Array (Nat × Nat × String) := #[]
  if msgs.hasErrors then
    for m in msgs.toList do
      if m.severity == .error then
        return #[(m.pos.line, m.pos.column + 1, s!"the proof file does not parse: {← m.data.toString}")]
  -- header: `import X` only, of the generated modules, other proofs, the library, Init
  let h := header.raw
  if !h[0].isNone || !h[1].isNone then
    out := out.push (1, 1, "`module` and `prelude` are not allowed in a proof file")
  for imp in h[2].getArgs do
    let n := imp[4].getId
    let (l, c) := posOf fm (imp.getPos?.getD 0)
    if !imp[0].isNone || !imp[1].isNone || !imp[3].isNone then
      out := out.push (l, c, s!"`{n}`: only plain `import` is allowed in a proof file (no public/meta/all)")
    else if !allowedImport n then
      let part := [`VReact, `Init].contains n.getRoot
      out := out.push (l, c, s!"`import {n}` is not allowed in a proof file: proof files may import the generated modules (VTS.…), other proof files (Proofs.…), the library (`import VReact`) and Init" ++
        (if part then s!"; not a part of the library or of Init (a file is checked in the environment of its imports, and {n} alone has the syntax of neither): write `import VReact`, or no import for Init alone" else ""))
    else if n.getRoot == `Proofs && !proofMods.contains n then
      out := out.push (l, c, s!"`import {n}`: there is no proof file proofs/{".".intercalate (n.components.drop 1 |>.map (·.toString (escape := false)))}.lean")
    else if n.getRoot == `Proofs && onCycle proofMods (moduleOfFile name) n then
      out := out.push (l, c, s!"`import {n}`: the proof files import each other in a cycle")
  unless out.isEmpty do return out
  let env ← envFor withLib cache enableInit
  let cmdCtx : Command.Context := { fileName := name, fileMap := fm, snap? := none, cancelTk? := none }
  let mut cmdState := Command.mkState env {} {}
  let mut pstate := pstate
  let mut issues : Array Issue := #[]
  repeat
    let scope := cmdState.scopes.head!
    let pmctx : ParserModuleContext := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps, msgs') := Parser.parseCommand inputCtx pmctx pstate {}
    pstate := ps
    if msgs'.hasErrors then
      for m in msgs'.toList do
        if m.severity == .error then
          return out.push (m.pos.line, m.pos.column + 1, s!"the proof file does not parse: {(← m.data.toString).trimAscii}")
    if cmd.isOfKind ``Command.eoi then break
    -- check, then elaborate the scope commands (namespaces activate scoped syntax)
    let act : CommandElabM (Array Issue) := do
      let ((), is) ← (checkCommand cmd).run #[]
      if is.isEmpty && scopeKinds.contains cmd.getKind then
        elabCommandTopLevel cmd
        let ns ← getCurrNamespace
        if reservedRoots.contains ns.getRoot then
          return #[{ pos := cmd.getPos?.getD 0, msg := s!"`namespace {ns}` is not allowed in a proof file: the namespaces VTS and VReact belong to the generated code and the library" }]
      return is
    match ← (act cmdCtx).run cmdState |>.toIO' with
    | .error e => return out.push (1, 1, s!"internal error of the proof check: {← e.toMessageData.toString}")
    | .ok (is, s) =>
      cmdState := s
      issues := issues ++ is
    -- (`#exit`, rejected above, ends the file for Lean too)
    if Parser.isTerminalCommand cmd then break
  for i in issues do
    let (l, c) := posOf fm i.pos
    out := out.push (l, c, i.msg)
  return out

end VReactProofCheck

open VReactProofCheck in
unsafe def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let input ← (← IO.getStdin).readToEnd
  let files ← match Json.parse input >>= fun j => j.getArr? with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"vreact-proofcheck: bad input: {e}"
  let cache ← IO.mkRef ((none, none) : Option Environment × Option Environment)
  let mut out : Array Json := #[]
  let mut inputs : Array (String × String) := #[]
  let mut proofMods : Std.HashMap Name (Array (Name × String.Pos.Raw)) := {}
  for f in files do
    let name ← IO.ofExcept (f.getObjValAs? String "name")
    let text ← IO.ofExcept (f.getObjValAs? String "text")
    inputs := inputs.push (name, text)
    proofMods := proofMods.insert (moduleOfFile name) (← headerImports name text)
  for (name, text) in inputs do
    let withLib := reachesLib proofMods (moduleOfFile name)
    for (l, c, msg) in ← checkFile name text withLib proofMods cache enableInitializersExecution do
      out := out.push (Json.mkObj [("file", name), ("line", l), ("col", c), ("msg", msg)])
  IO.println (Json.arr out).compress
  return 0
