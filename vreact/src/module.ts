/**
 * Program-level driver: loads the TypeScript program, checks it, collects
 * declarations, and emits one Lean project with two files per TS module:
 *
 *   VTS/<Mod>/Defs.lean — types, constants, pure functions (+ inline obligations)
 *   VTS/<Mod>/View.lean — postconditions, component specs and renders
 *
 * User lemmas in `proofs/<Mod>.lean` sit between the two (they may mention the
 * definitions and are available to every obligation of the views).
 */
import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { Program, ModCtx, type Obligation, type FnInfo, type CompInfo, type Global, type ConstInfo } from "./ctx.ts";
import { T, type VType, typeOfNode, typeOfDecl, emitTypeDecl, leanType } from "./types.ts";
import { VtsError, fail, leanIdent, leanField, leanStr, paren, capitalize, nodeText } from "./util.ts";
import { expr, prop, propAll, valueBlock, specFn, symbolOf, bindParam, typeOf } from "./translate.ts";
import { translateComponent, compSignature, baseEnv } from "./component.ts";

export interface Config {
  root: string;
  srcDir: string;
  files: string[];
  outDir: string;
  proofsDir: string;
  leanLib: string;
}

export interface ModuleResult {
  tsFile: string;
  ns: string;
  defsModule: string;
  viewModule: string;
  components: { name: string; ns: string; trusted: boolean; line: number }[];
  certificates: { name: string; qname: string }[];
  functions: { name: string; qname: string; trusted: boolean; posts: string[] }[];
}

export interface TranslateResult {
  ok: boolean;
  tsDiagnostics: string[];
  errors: VtsError[];
  modules: ModuleResult[];
  obligations: Obligation[];
}

const SPEC_RE = /vreact[\\/](spec|lib)|vreact-spec/;

function loadProgram(cfg: Config): { program: ts.Program; diags: string[] } {
  const cfgPath = ts.findConfigFile(cfg.root, ts.sys.fileExists, "tsconfig.json");
  let options: ts.CompilerOptions = {
    strict: true,
    jsx: ts.JsxEmit.ReactJSX,
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    skipLibCheck: true,
    noEmit: true,
    allowImportingTsExtensions: true,
  };
  if (cfgPath && path.dirname(cfgPath) === cfg.root) {
    const raw = ts.readConfigFile(cfgPath, ts.sys.readFile);
    const parsed = ts.parseJsonConfigFileContent(raw.config, ts.sys, path.dirname(cfgPath));
    options = { ...parsed.options, noEmit: true };
  }
  const diags: string[] = [];
  if (!options.strict && !options.strictNullChecks) diags.push("tsconfig: VTS requires \"strict\": true (null safety is part of the model)");
  const program = ts.createProgram(cfg.files, options);
  const host: ts.FormatDiagnosticsHost = {
    getCanonicalFileName: (f) => f,
    getCurrentDirectory: () => cfg.root,
    getNewLine: () => "\n",
  };
  for (const f of cfg.files) {
    const sf = program.getSourceFile(f);
    if (!sf) {
      diags.push(`cannot load ${f}`);
      continue;
    }
    const ds = ts.getPreEmitDiagnostics(program, sf).filter((d) => d.category === ts.DiagnosticCategory.Error);
    for (const d of ds) diags.push(ts.formatDiagnostic(d, host).trim());
  }
  return { program, diags };
}

function sanitizeSeg(s: string): string {
  const t = s.replace(/[^A-Za-z0-9_]/g, "_");
  return /^[A-Za-z_]/.test(t) ? t : "M" + t;
}

function isComponentDecl(fn: ts.FunctionDeclaration): boolean {
  const name = fn.name?.text ?? "";
  if (!/^[A-Z]/.test(name)) return false;
  if (fn.type && /JSX\.Element|ReactNode|ReactElement/.test(fn.type.getText())) return true;
  let jsx = false;
  const visit = (n: ts.Node) => {
    if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n)) jsx = true;
    if (!jsx) ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return jsx;
}

function isTrusted(n: ts.Node): boolean {
  return ts.getJSDocTags(n).some((t) => t.tagName.text === "trusted");
}
function isOpaque(n: ts.Node): boolean {
  return ts.getJSDocTags(n).some((t) => t.tagName.text === "opaque");
}

export function translate(cfg: Config): TranslateResult {
  const { program, diags } = loadProgram(cfg);
  const res: TranslateResult = { ok: false, tsDiagnostics: diags, errors: [], modules: [], obligations: [] };
  if (diags.length) return res;
  const checker = program.getTypeChecker();
  const fileSet = new Set(cfg.files.map((f) => path.resolve(f)));
  const nsOfFile = (f: string) => {
    const rel = path.relative(cfg.srcDir, f).replace(/\.(tsx?|jsx?)$/, "");
    return "VTS." + rel.split(path.sep).map(sanitizeSeg).join(".");
  };
  const prog = new Program(checker, cfg.root, (sf) => nsOfFile(sf.fileName));
  const sfs = cfg.files.map((f) => program.getSourceFile(f)!);
  const counter = { n: 0 };

  // ---- import graph & topological order ----
  const importsOf = new Map<ts.SourceFile, ts.SourceFile[]>();
  for (const sf of sfs) {
    const deps: ts.SourceFile[] = [];
    for (const st of sf.statements) {
      if (!ts.isImportDeclaration(st)) continue;
      const spec = (st.moduleSpecifier as ts.StringLiteral).text;
      if (spec === "react" || spec === "react/jsx-runtime") continue;
      const sym = checker.getSymbolAtLocation(st.moduleSpecifier);
      const target = sym?.valueDeclaration?.getSourceFile() ?? (sym?.declarations?.[0] as ts.SourceFile | undefined);
      if (target && SPEC_RE.test(target.fileName)) continue;
      if (SPEC_RE.test(spec)) continue;
      if (!target || !fileSet.has(path.resolve(target.fileName))) {
        res.errors.push(new VtsError(st, `import of "${spec}" is outside the verified program (only react, vreact/spec, and other VTS modules may be imported)`));
        continue;
      }
      deps.push(target as ts.SourceFile);
    }
    importsOf.set(sf, deps);
  }
  const order: ts.SourceFile[] = [];
  const state = new Map<ts.SourceFile, number>();
  const visit = (sf: ts.SourceFile, stack: ts.SourceFile[]) => {
    const st = state.get(sf);
    if (st === 2) return;
    if (st === 1) {
      res.errors.push(new VtsError(sf.statements[0], `import cycle: ${[...stack, sf].map((s) => path.basename(s.fileName)).join(" → ")}`));
      return;
    }
    state.set(sf, 1);
    for (const d of importsOf.get(sf) ?? []) visit(d, [...stack, sf]);
    state.set(sf, 2);
    order.push(sf);
  };
  for (const sf of sfs) visit(sf, []);
  if (res.errors.length) return res;

  // ---- declaration prepass ----
  const mods = new Map<ts.SourceFile, ModCtx>();
  for (const sf of order) {
    const ns = nsOfFile(sf.fileName);
    const m = new ModCtx(prog, ns, sf, res.obligations, counter);
    mods.set(sf, m);
    for (const st of sf.statements) {
      try {
        collect(st, m, ns, res);
      } catch (e) {
        if (e instanceof VtsError) res.errors.push(e);
        else throw e;
      }
    }
  }
  if (res.errors.length) return res;

  // ---- translation ----
  fs.mkdirSync(cfg.outDir, { recursive: true });
  const leanFiles: { rel: string; text: string }[] = [];
  const proofModules = new Set<string>();
  // copy user proofs
  if (fs.existsSync(cfg.proofsDir)) {
    const walk = (d: string) => {
      for (const f of fs.readdirSync(d)) {
        const p = path.join(d, f);
        if (fs.statSync(p).isDirectory()) walk(p);
        else if (f.endsWith(".lean")) {
          const rel = path.relative(cfg.proofsDir, p);
          leanFiles.push({ rel: path.join("Proofs", rel), text: fs.readFileSync(p, "utf8") });
          proofModules.add("Proofs." + rel.replace(/\.lean$/, "").split(path.sep).join("."));
        }
      }
    };
    walk(cfg.proofsDir);
  }
  for (const sf of order) {
    const m = mods.get(sf)!;
    const ns = m.ns;
    const modRes: ModuleResult = { tsFile: sf.fileName, ns, defsModule: `${ns}.Defs`, viewModule: `${ns}.View`, components: [], functions: [], certificates: [] };
    const deps = (importsOf.get(sf) ?? []).map((d) => nsOfFile(d.fileName));
    const rel = ns.split(".").join(path.sep);
    const proofMod = "Proofs." + ns.split(".").slice(1).join(".");
    let defs = header([...deps.map((d) => `${d}.Defs`), ...(proofModules.has("Proofs.Base") ? ["Proofs.Base"] : [])]) + `namespace ${ns}\n\n`;
    let view = header([`${ns}.Defs`, ...deps.map((d) => `${d}.View`), ...(proofModules.has(proofMod) ? [proofMod] : [])]) + `namespace ${ns}\n\n`;
    try {
      // types declared in this module
      for (const nt of prog.reg.order) {
        if (nt.module !== ns) continue;
        // props types with callbacks are represented by the component's Props/Cb structures
        if (nt.def.k === "rec" && nt.def.fields.some((f) => f.type.k === "fn" || (f.type.k === "opt" && f.type.elem.k === "fn"))) continue;
        defs += emitTypeDecl(nt, prog.reg) + "\n";
      }
      // constants & functions, dependency-ordered
      const decls = sortDecls(sf, m);
      for (const d of decls) {
        const g = prog.globals.get(d)!;
        if (g.k === "const") defs += translateConst(d as ts.VariableDeclaration, g.info, m) + "\n";
        if (g.k === "fn") {
          const r = translateFunction(d as ts.FunctionDeclaration, g.info, m);
          defs += r.def + "\n";
          if (r.post) view += r.post + "\n";
          modRes.functions.push({ name: g.info.name, qname: g.info.qname, trusted: g.info.trusted, posts: r.postNames });
        }
      }
      // components, children first
      for (const c of sortComponents(sf, m)) {
        const g = prog.globals.get(c) as { k: "comp"; info: CompInfo };
        view += translateComponent(c as ts.FunctionDeclaration, g.info, m) + "\n";
        const { line } = sf.getLineAndCharacterOfPosition(c.getStart(sf));
        modRes.components.push({ name: g.info.name, ns: g.info.ns, trusted: g.info.trusted, line: line + 1 });
      }
      // application roots (no props): element + whole-app soundness certificate
      for (const c of sortComponents(sf, m)) {
        const g = prog.globals.get(c) as { k: "comp"; info: CompInfo };
        const info = g.info;
        if (info.data.length || info.callbacks.length) continue;
        const N = info.ns;
        view += `/-- \`<${info.name}/>\` as the root element of an application. -/\n`;
        view += `theorem ${info.name}.root_pre : ${N}.pre ${N}.Props.mk :=\n  ${m.ob(c, "root-precondition", `<${info.name}/> can be mounted as the application root`)}\n\n`;
        view += `noncomputable def ${info.name}.element : VReact.CompNode Empty :=\n  ⟨${N}.spec, ${N}.Props.mk, ${N}.Cb.mk, ${N}.root_pre,\n   fun s h => ${N}.component.render ${N}.Props.mk ${N}.Cb.mk s ${N}.root_pre h⟩\n\n`;
        view += `/-- **Certificate.** In every run of the application rooted at \`<${info.name}/>\` — any sequence of\nuser events, effect flushes and timer callbacks — every mounted component instance satisfies\nits invariant (instantiation of \`VReact.run_allInv\`). -/\n`;
        view += `theorem ${info.name}.certificate (fuel : Nat) (acts : List VReact.Action) :\n    (VReact.run fuel ${info.name}.element acts).AllInv :=\n  VReact.run_allInv fuel ${info.name}.element acts\n\n`;
        modRes.certificates.push({ name: info.name, qname: `${ns}.${info.name}.certificate` });
      }
      // (axiom reports are printed after the namespace is closed, with full names)
    } catch (e) {
      if (e instanceof VtsError) {
        res.errors.push(e);
        continue;
      }
      throw e;
    }
    defs += `\nend ${ns}\n#eval "vreact:checked"\n`;
    view += `\nend ${ns}\n\n`;
    for (const c of modRes.components) view += `#print axioms ${c.ns}.component\n`;
    for (const c of modRes.certificates) view += `#print axioms ${c.qname}\n`;
    for (const f of modRes.functions) {
      view += `#print axioms ${f.qname}\n`;
      for (const p of f.posts) view += `#print axioms ${p}\n`;
    }
    view += `#eval "vreact:checked"\n`;
    leanFiles.push({ rel: path.join(rel, "Defs.lean"), text: defs });
    leanFiles.push({ rel: path.join(rel, "View.lean"), text: view });
    res.modules.push(modRes);
  }
  if (res.errors.length) return res;
  // root module and lake project
  const rootImports = res.modules.map((mr) => `import ${mr.viewModule}`).join("\n");
  leanFiles.push({ rel: "VTS.lean", text: rootImports + "\n" });
  const libs = [`[[lean_lib]]\nname = "VTS"\n`];
  if (proofModules.size) libs.push(`[[lean_lib]]\nname = "Proofs"\n`);
  const lakefile = `name = "vts"\ndefaultTargets = ["VTS"]\n\n[[require]]\nname = "VReact"\npath = ${JSON.stringify(cfg.leanLib)}\n\n${libs.join("\n")}`;
  leanFiles.push({ rel: "lakefile.toml", text: lakefile });
  leanFiles.push({ rel: "lean-toolchain", text: fs.readFileSync(path.join(cfg.leanLib, "lean-toolchain"), "utf8") });
  // write, removing stale generated files
  fs.rmSync(path.join(cfg.outDir, "VTS"), { recursive: true, force: true });
  fs.rmSync(path.join(cfg.outDir, "Proofs"), { recursive: true, force: true });
  for (const f of leanFiles) {
    const p = path.join(cfg.outDir, f.rel);
    fs.mkdirSync(path.dirname(p), { recursive: true });
    if (!fs.existsSync(p) || fs.readFileSync(p, "utf8") !== f.text) fs.writeFileSync(p, f.text);
  }
  res.ok = true;
  return res;
}

function header(imports: string[]): string {
  return [
    "/- Generated by vreact from VTS sources. Do not edit: edit the .tsx file. -/",
    "import VReact",
    ...imports.map((i) => `import ${i}`),
    "open VReact",
    "set_option linter.unusedVariables false",
    "set_option maxHeartbeats 1000000",
    "noncomputable section",
    "",
  ].join("\n");
}

/* ───────────────────────── declaration prepass ───────────────────────── */

function collect(st: ts.Statement, m: ModCtx, ns: string, res: TranslateResult) {
  const prog = m.prog;
  if (ts.isImportDeclaration(st)) return;
  if (ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) {
    typeOfDecl(st, prog.typeEnv);
    return;
  }
  if (ts.isFunctionDeclaration(st)) {
    if (!st.name) fail(st, "functions need a name");
    if (st.asteriskToken || st.modifiers?.some((x) => x.kind === ts.SyntaxKind.AsyncKeyword)) fail(st, "async functions and generators are not supported");
    if (st.typeParameters?.length) fail(st, "generic functions are not supported in VTS yet");
    const trusted = isTrusted(st);
    if (isComponentDecl(st)) {
      const info = compSignature(st, ns, ns, m, trusted);
      prog.globals.set(st, { k: "comp", info });
      return;
    }
    if (/^use[A-Z]/.test(st.name.text)) fail(st, "custom hooks are not supported yet: inline the hook calls into the component");
    const params = st.parameters.map((p) => {
      if (!p.type) fail(p, "parameters need type annotations");
      if (p.initializer || p.dotDotDotToken || p.questionToken) fail(p, "default/rest/optional parameters are not supported");
      if (!ts.isIdentifier(p.name)) fail(p, "destructured parameters are not supported in top-level functions");
      return { name: p.name.text, type: typeOfNode(p.type, prog.typeEnv, capitalize(st.name!.text) + capitalize(p.name.text)) };
    });
    if (!st.type) fail(st, "functions need a return type annotation");
    const ret = typeOfNode(st.type, prog.typeEnv, capitalize(st.name.text) + "Result");
    const hasPre = !!st.body?.statements.some((s) => isSpecCall(s, m, "requires"));
    const info: FnInfo = { qname: `${ns}.${leanIdent(st.name.text)}`, name: st.name.text, params, ret, hasPre, trusted, opaque: isOpaque(st), decl: st, module: ns };
    prog.globals.set(st, { k: "fn", info });
    return;
  }
  if (ts.isVariableStatement(st)) {
    if (!(st.declarationList.flags & ts.NodeFlags.Const)) fail(st, "top-level variables must be const");
    for (const d of st.declarationList.declarations) {
      if (!ts.isIdentifier(d.name) || !d.initializer) fail(d, "top-level const needs a name and initializer");
      let t: VType | undefined = d.type ? typeOfNode(d.type, prog.typeEnv, capitalize(d.name.text)) : undefined;
      if (!t) {
        const init = d.initializer;
        if (ts.isNumericLiteral(init)) t = /[.eE]/.test(init.text) ? T.num : T.int;
        else if (ts.isPrefixUnaryExpression(init) && ts.isNumericLiteral(init.operand)) t = T.int;
        else if (ts.isStringLiteralLike(init)) t = T.str;
        else if (init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword) t = T.bool;
        else fail(d, "annotate the type of this constant");
      }
      prog.globals.set(d, { k: "const", info: { qname: `${ns}.${leanIdent(d.name.text)}`, type: t, decl: d, opaque: isOpaque(d) || isOpaque(st), facts: [] } });
    }
    return;
  }
  if (ts.isExportAssignment(st) || ts.isExportDeclaration(st)) return;
  // module-level assert(fact): a proved fact about @opaque constants
  if (ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) && isSpecCall(st, m, "assert")) {
    const fact = st.expression.arguments[0];
    let owner: { info: { facts: ts.Expression[]; opaque: boolean } } | null = null;
    const visit = (n: ts.Node) => {
      if (owner) return;
      if (ts.isIdentifier(n)) {
        let s = m.checker.getSymbolAtLocation(n);
        if (s && s.flags & ts.SymbolFlags.Alias) s = m.checker.getAliasedSymbol(s);
        const g = s?.declarations?.[0] ? prog.globals.get(s.declarations[0]) : undefined;
        if (g?.k === "const" && g.info.opaque) owner = g as { info: ConstInfo };
      }
      ts.forEachChild(n, visit);
    };
    visit(fact);
    if (!owner) fail(st, "a module-level assert(…) states a fact about an /** @opaque */ constant declared above it");
    (owner as { info: { facts: ts.Expression[] } }).info.facts.push(fact);
    return;
  }
  if (ts.isEmptyStatement(st)) return;
  fail(st, `top-level statement not supported in VTS (only imports, types, functions, components and constants)`);
}

function isSpecCall(s: ts.Statement, m: ModCtx, name: string): boolean {
  if (!ts.isExpressionStatement(s) || !ts.isCallExpression(s.expression)) return false;
  const env = baseEnv(m);
  return specFn(env, s.expression.expression) === name;
}

/** Order constants and functions of a module so definitions precede uses. */
function sortDecls(sf: ts.SourceFile, m: ModCtx): ts.Node[] {
  const decls: ts.Node[] = [];
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && m.prog.globals.get(st)?.k === "fn") decls.push(st);
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (m.prog.globals.get(d)?.k === "const") decls.push(d);
  }
  return topo(decls, m, (g) => g.k === "fn" || g.k === "const");
}

function sortComponents(sf: ts.SourceFile, m: ModCtx): ts.Node[] {
  const comps = sf.statements.filter((st) => ts.isFunctionDeclaration(st) && m.prog.globals.get(st)?.k === "comp");
  return topo(comps, m, (g) => g.k === "comp");
}

function topo(decls: ts.Node[], m: ModCtx, rel: (g: Global) => boolean): ts.Node[] {
  const set = new Set(decls);
  const out: ts.Node[] = [];
  const st = new Map<ts.Node, number>();
  const refs = (d: ts.Node): ts.Node[] => {
    const r: ts.Node[] = [];
    const visit = (n: ts.Node) => {
      if (ts.isIdentifier(n)) {
        let s = m.checker.getSymbolAtLocation(n);
        if (s && s.flags & ts.SymbolFlags.Alias) s = m.checker.getAliasedSymbol(s);
        const dd = s?.declarations?.[0];
        if (dd && dd !== d && set.has(dd)) {
          const g = m.prog.globals.get(dd);
          if (g && rel(g)) r.push(dd);
        }
      }
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(d, visit);
    return r;
  };
  const go = (d: ts.Node) => {
    const s = st.get(d);
    if (s === 2) return;
    if (s === 1) fail(d, "mutually recursive declarations are not supported");
    st.set(d, 1);
    for (const x of refs(d)) go(x);
    st.set(d, 2);
    out.push(d);
  };
  for (const d of decls) go(d);
  return out;
}

/* ───────────────────────── constants & functions ───────────────────────── */

function translateConst(d: ts.VariableDeclaration, info: ConstInfo, m: ModCtx): string {
  const env = baseEnv(m);
  const v = expr(d.initializer!, env, info.type);
  const short = leanIdent((d.name as ts.Identifier).text);
  // transparent constants are unfolded by automation; @opaque ones only through their facts
  let out = `${info.opaque ? "" : "@[vreact_simp, reducible] "}def ${short} : ${leanType(info.type)} :=\n  ${v.code}\n`;
  info.facts.forEach((f, k) => {
    const name = k === 0 ? `${short}.post` : `${short}.post${k + 1}`;
    out += `\n/-- fact: ${nodeText(f, 80)} -/\ntheorem ${name} : ${prop(f, env)} := by\n  unfold ${short}\n  exact ${m.ob(f, "fact", `fact about ${short}: ${nodeText(f, 60)}`)}\n`;
  });
  return out;
}

function hasHole(fn: ts.FunctionDeclaration): boolean {
  let found = false;
  const visit = (n: ts.Node) => {
    if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === "hole") found = true;
    if (!found) ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return found;
}

function translateFunction(fn: ts.FunctionDeclaration, info: FnInfo, m: ModCtx): { def: string; post: string | null; postNames: string[] } {
  let env = baseEnv(m);
  const binders: string[] = [];
  const argNames: string[] = [];
  fn.parameters.forEach((p, i) => {
    const r = bindParam(p.name, info.params[i].type, env);
    env = r.env;
    binders.push(`(${r.binder} : ${leanType(info.params[i].type)})`);
    argNames.push(r.binder);
  });
  const stmts = [...(fn.body?.statements ?? [])];
  const hyps: string[] = [];
  const hypNames: string[] = [];
  const reqs: ts.Expression[] = [];
  const posts: { lam: ts.ArrowFunction | ts.FunctionExpression }[] = [];
  while (stmts.length && ts.isExpressionStatement(stmts[0]) && ts.isCallExpression(stmts[0].expression)) {
    const c = stmts[0].expression;
    const sf = specFn(env, c.expression);
    if (sf === "requires") {
      if (c.arguments.length !== 1) fail(c, "requires(condition)");
      reqs.push(c.arguments[0]);
    } else if (sf === "ensures") {
      const lam = c.arguments[0];
      if (!lam || !(ts.isArrowFunction(lam) || ts.isFunctionExpression(lam)) || lam.parameters.length !== 1) fail(c, "ensures((result) => condition)");
      posts.push({ lam });
    } else if (sf === "decreases") {
      fail(c, "recursion is not supported yet");
    } else break;
    stmts.shift();
  }
  // all requires form one precondition (each guarded by the earlier ones): call sites pass one proof
  if (reqs.length) {
    hyps.push(`(h_pre : ${propAll(reqs, env)})`);
    hypNames.push("h_pre");
  }
  const short = leanIdent(info.name);
  const sig = `${short} ${binders.join(" ")} ${hyps.join(" ")} : ${leanType(info.ret)}`.replace(/\s+/g, " ");
  let def: string;
  if (info.trusted) {
    def = `/-- @trusted: body not verified, contract assumed. -/\naxiom ${sig}\n`;
  } else {
    // self-recursion check
    let rec = false;
    const visit = (n: ts.Node) => {
      if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === info.name) rec = true;
      ts.forEachChild(n, visit);
    };
    stmts.forEach(visit);
    if (rec) fail(fn, "recursion is not supported yet: use array methods or for…of");
    const body = valueBlock(stmts, env, info.ret, fn);
    def = `${info.opaque ? "" : "@[vreact_simp, reducible] "}def ${sig} :=\n  ${body.code}\n`;

  }
  let post: string | null = null;
  const postNames: string[] = [];
  if (posts.length) {
    const call = `(${info.qname}${argNames.map((a) => " " + a).join("")}${hypNames.map((h) => " " + h).join("")})`;
    const kw = info.trusted ? "axiom" : "theorem";
    const parts: string[] = [];
    posts.forEach(({ lam }, k) => {
      const p = lam.parameters[0];
      if (!ts.isIdentifier(p.name)) fail(p, "result parameter must be an identifier");
      const e2 = { ...env, vars: new Map(env.vars) };
      e2.vars.set(symbolOf(env, p.name)!, { k: "val", code: call, type: info.ret });
      const body = lam.body;
      if (ts.isBlock(body)) fail(body, "ensures body must be an expression");
      const stmt = prop(body, e2);
      const name = k === 0 ? `${short}.post` : `${short}.post${k + 1}`;
      postNames.push(`${info.qname}.${k === 0 ? "post" : `post${k + 1}`}`);
      // opaque functions are not unfolded by callers: their postconditions are proved by
      // unfolding once here, then used through E-matching on calls (grind_pattern below)
      // a function whose body still contains hole() has no implementation yet: contract pending
      const pending = hasHole(fn);
      const ob = info.trusted || pending ? "" : m.ob(lam, "postcondition", `postcondition of ${info.name}: ${nodeText(body, 70)}`);
      const proof = info.trusted ? "" : pending ? ` :=\n  sorry /- pending: hole() -/` : info.opaque ? ` := by\n  unfold ${short}\n  exact ${ob}` : ` :=\n  ${ob}`;
      let t = `${kw} ${name} ${binders.join(" ")} ${hyps.join(" ")} :\n    ${stmt}${proof}\n`;
      parts.push(t);
    });
    post = parts.join("\n");
  }
  return { def, post, postNames };
}
