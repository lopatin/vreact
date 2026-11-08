import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { TypeRegistry, type VType, type Param, type Field, type TypeEnv } from "./types.ts";
import { relLoc, nodeText, subscripted } from "./util.ts";

/** A translated Lean term together with its VTS type. */
export interface Val {
  code: string;
  type: VType;
}

/** Information about a pure top-level function. */
export interface FnInfo {
  qname: string;
  name: string;
  params: Param[];
  ret: VType;
  hasPre: boolean;
  trusted: boolean;
  /** @opaque: callers reason only through the contract (no unfolding) */
  opaque: boolean;
  decl: ts.FunctionDeclaration;
  module: string;
}

export interface ConstInfo {
  qname: string;
  type: VType;
  decl: ts.VariableDeclaration;
  /** @opaque: not unfolded by automation; facts come from module-level assert(…) */
  opaque: boolean;
  /** module-level facts about this constant (assert statements) */
  facts: ts.Expression[];
}

export interface CallbackInfo {
  name: string;
  params: Param[];
}

/** What a parent needs to know about a child component. */
export interface CompInfo {
  name: string;
  /** Lean namespace of the component (e.g. VTS.Board.Column). */
  ns: string;
  module: string;
  data: Field[];
  callbacks: CallbackInfo[];
  decl: ts.FunctionDeclaration;
  trusted: boolean;
  propsType: VType | null;
}

export type Global =
  | { k: "fn"; info: FnInfo }
  | { k: "const"; info: ConstInfo }
  | { k: "comp"; info: CompInfo };

export interface Obligation {
  id: number;
  kind: string;
  desc: string;
  where: string;
  file: string;
  line: number;
}

/** State variable of a component (one useState / useReducer slot). */
export interface StateVar {
  name: string;
  field: string;
  type: VType;
  reducer?: FnInfo;
  actionType?: VType;
}

export interface CompCtx {
  info: CompInfo;
  stateType: string;
  stateVars: StateVar[];
  /** Lean name of the props data parameter. */
  propsVar: string;
  /** Lean name of the callbacks record. */
  cbVar: string;
  /** Lean name of the snapshot state. */
  snap: string;
  invName: string;
}

export interface HandlerAcc {
  kind: "discrete" | "robust";
  updates: string[];
  emit: string | null;
  /** Lean name of the event parameter (if any). */
  eventVar: string | null;
}

export type Binding =
  /**
   * `ts`: the TypeScript type of the value, when that of the identifier says nothing (`any`): the
   * parameter of an unannotated `ensures((r) => …)` (the declared return type), or of a callback
   * whose context is `any` (`r.every((x) => …)`: the element type of `r`'s real type)
   */
  | { k: "val"; code: string; type: VType; ts?: ts.Type }
  | { k: "setter"; sv: StateVar }
  | { k: "dispatch"; sv: StateVar }
  | { k: "closure"; fn: ts.ArrowFunction | ts.FunctionExpression; env: Env }
  | { k: "callback"; cb: CallbackInfo }
  | { k: "props" }
  | { k: "event"; leanVar: string }
  /** a JSX const: translated (obligations checked) at its declaration, bound to the Lean local `code` */
  | { k: "jsx"; node: ts.Expression; env: Env; code: string };

export interface Narrowed {
  /** narrowed value (Option payload / variant) */
  kind: "some" | "variant";
  code: string;
  type: VType;
  variant?: string;
  fields?: Map<string, Val>;
}

/** A translated `hole<T>()` and the environment in effect there (read by `vreact synth`). */
export interface HoleEnv {
  node: ts.CallExpression;
  env: Env;
}

export interface Env {
  m: ModCtx;
  vars: Map<ts.Symbol, Binding>;
  narrow: Map<string, Narrowed>;
  /** Lean names in scope (for capture-avoiding naming). */
  scope: Set<string>;
  mode: "code" | "spec";
  comp?: CompCtx;
  handler?: HandlerAcc;
  /** inside a functional update `setX(prev => …)` / reducer argument: current-state access */
  curState?: string;
  /** Lean hypotheses in scope that justify obligations (names only, for documentation). */
  fnName?: string;
  /** the key function of a keyed `.map`: its JSX consts are translated by the node function */
  keyFn?: boolean;
  /**
   * Set only while `vreact synth` records hole environments (`Program.holeEnvs`), and read only
   * by synth: the variants a union-typed path can still have here, where tests excluded the
   * others but the translation kept one `_` arm (several variants were left). Code there that
   * needs one of them makes the translator split that arm per variant (see narrowBranch).
   */
  remaining?: Map<string, string[]>;
}

/** The module of the contract functions and `int`. */
export const SPEC_MODULE = "vreact/spec";
/** This tool's own declarations of vreact/spec (real path). */
const OWN_SPEC = (() => {
  const p = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "spec", "index.d.ts");
  try {
    return fs.realpathSync(p);
  } catch {
    return p;
  }
})();
/** Declaration files of React (its types package, or the package itself). */
const REACT_FILE_RE = /[\\/]node_modules[\\/](@types[\\/])?react[\\/]/;

/** The source file a module specifier (`"./x"`, `"vreact/spec"`) resolves to, if any. */
export function moduleFile(checker: ts.TypeChecker, spec: ts.Expression): ts.SourceFile | undefined {
  const sym = checker.getSymbolAtLocation(spec);
  const d = sym?.valueDeclaration ?? sym?.declarations?.[0];
  return d && ts.isSourceFile(d) ? d : d?.getSourceFile();
}

/**
 * Per-program translation context.
 *
 * Builtins — JavaScript's globals (`undefined`, `Math`, `String`, `console`, …), lib types
 * (`ReadonlyArray`), React's hooks and types, vreact/spec's functions and `int` — are recognised
 * by the declaration a name resolves to, never by its spelling: a local, a parameter, an import
 * alias or a project declaration spelled like one is the user's binding (`isGlobal`, `specName`,
 * `reactName`).
 */
export class Program {
  checker: ts.TypeChecker;
  tsProgram: ts.Program;
  reg = new TypeRegistry();
  globals = new Map<ts.Node, Global>();
  root: string;
  typeEnv: TypeEnv;
  modNs = new Map<string, string>();
  /** the declaration files `import … from "vreact/spec"` resolves to (library files only) */
  specFiles = new Set<ts.SourceFile>();
  /** set by `vreact synth`: every translation of a `hole<T>()` kept in the output, with its environment (narrowing) */
  holeEnvs?: HoleEnv[];
  constructor(tsProgram: ts.Program, root: string, nsOf: (sf: ts.SourceFile) => string, projectFiles: readonly ts.SourceFile[]) {
    const checker = tsProgram.getTypeChecker();
    this.tsProgram = tsProgram;
    this.checker = checker;
    this.root = root;
    for (const sf of projectFiles) {
      for (const st of sf.statements) {
        if (!(ts.isImportDeclaration(st) || ts.isExportDeclaration(st)) || !st.moduleSpecifier || !ts.isStringLiteral(st.moduleSpecifier)) continue;
        if (st.moduleSpecifier.text !== SPEC_MODULE) continue;
        const target = moduleFile(checker, st.moduleSpecifier);
        if (target && this.isLibraryFile(target)) this.specFiles.add(target);
      }
    }
    this.typeEnv = {
      checker,
      reg: this.reg,
      nsOf,
      // `int` of vreact/spec, also through aliases (`import { type int as I }`, `type Count = int`
      // resolves through typeOfDecl); a project type spelled `int` is the project's
      isSpecInt: (node) => this.specName(ts.isQualifiedName(node.typeName) ? node.typeName.right : node.typeName) === "int",
      isLibType: (node, names) => {
        const s = this.resolve(this.checker.getSymbolAtLocation(ts.isQualifiedName(node.typeName) ? node.typeName.right : node.typeName));
        return !!s && names.includes(s.name) && this.declaredIn(s, (f) => this.isLibraryFile(f)) ? s.name : null;
      },
      isLibraryFile: (sf) => this.isLibraryFile(sf),
      isReactType: (node, names) => {
        const n = this.reactName(ts.isQualifiedName(node.typeName) ? node.typeName.right : node.typeName);
        return n && names.includes(n) ? n : null;
      },
    };
  }
  /**
   * A file of TypeScript's standard library, of an external library (found in node_modules), or
   * vreact's own spec declarations (however the project resolves them): not the project's.
   */
  isLibraryFile(sf: ts.SourceFile): boolean {
    return this.tsProgram.isSourceFileDefaultLibrary(sf) || this.tsProgram.isSourceFileFromExternalLibrary(sf) || path.resolve(sf.fileName) === OWN_SPEC;
  }
  isReactFile(sf: ts.SourceFile): boolean {
    return this.isLibraryFile(sf) && REACT_FILE_RE.test(sf.fileName);
  }
  /** The symbol an import alias stands for (other symbols unchanged). */
  resolve(s: ts.Symbol | undefined): ts.Symbol | undefined {
    if (s && s.flags & ts.SymbolFlags.Alias) return this.checker.getAliasedSymbol(s);
    return s;
  }
  /** Is every declaration of `s` in a file accepted by `pred` (and is there one)? */
  declaredIn(s: ts.Symbol | undefined, pred: (sf: ts.SourceFile) => boolean): boolean {
    const ds = s?.declarations;
    return !!ds?.length && ds.every((d) => pred(d.getSourceFile()));
  }
  /**
   * Does `n` refer to the JavaScript global `name` (`undefined`, `Math`, `String`, `console`,
   * `localStorage`, `document`, `setTimeout`, …): declared only by the libraries, not shadowed by a
   * local, parameter, import or project declaration?
   */
  isGlobal(n: ts.Node, name: string): boolean {
    if (!ts.isIdentifier(n) || n.text !== name) return false;
    const s = this.checker.getSymbolAtLocation(n);
    if (!s) return false;
    if (name === "undefined") return this.checker.isUndefinedSymbol(s);
    return !(s.flags & ts.SymbolFlags.Alias) && this.declaredIn(s, (f) => this.isLibraryFile(f));
  }
  /** The name of the vreact/spec declaration (function or `int`) that `n` refers to, through import aliases. */
  specName(n: ts.Node): string | null {
    if (!ts.isIdentifier(n)) return null;
    const s = this.resolve(this.checker.getSymbolAtLocation(n));
    return s && this.declaredIn(s, (f) => this.specFiles.has(f)) ? s.name : null;
  }
  /** The name of the React declaration (hook, type) that `n` refers to, through import aliases. */
  reactName(n: ts.Node): string | null {
    if (!ts.isIdentifier(n)) return null;
    const s = this.resolve(this.checker.getSymbolAtLocation(n));
    return s && this.declaredIn(s, (f) => this.isReactFile(f)) ? s.name : null;
  }
}

/** Per generated Lean file context: obligations and fresh names. */
export class ModCtx {
  prog: Program;
  ns: string;
  obligations: Obligation[];
  counter: { n: number };
  hyp = 0;
  /** a throw-away context for type queries (its terms are discarded) */
  dry = false;
  /** imported modules needed by this file (Lean module names) */
  deps: Set<string>;
  sf: ts.SourceFile;
  constructor(prog: Program, ns: string, sf: ts.SourceFile, obligations: Obligation[], counter: { n: number }) {
    this.prog = prog;
    this.ns = ns;
    this.sf = sf;
    this.obligations = obligations;
    this.counter = counter;
    this.deps = new Set();
  }
  get checker() {
    return this.prog.checker;
  }
  get reg() {
    return this.prog.reg;
  }
  /** A fresh hypothesis name (subscripted: never a VTS identifier's Lean name, see util.ts). */
  fresh(base: string): string {
    this.hyp++;
    return subscripted(base, this.hyp);
  }
  /** Emit a proof obligation discharged by `vreact_auto`, tagged with a source marker;
   * `vreact_ob` gives it its own heartbeat budget (VReact/Budget.lean). */
  ob(node: ts.Node, kind: string, desc: string, tactic = "vreact_auto"): string {
    const id = ++this.counter.n;
    const sf = node.getSourceFile();
    const { line } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    this.obligations.push({ id, kind, desc, where: relLoc(node, this.prog.root), file: sf.fileName, line: line + 1 });
    return `(/-⟦ob${id}⟧-/ by vreact_ob ${tactic})`;
  }
  obCount(): number {
    return this.obligations.length;
  }
  /** Run a translation only for the checks it makes (its term is discarded): the
   * obligations it registers are withdrawn, so none is left unemitted. */
  dryRun(f: () => void) {
    const n = this.counter.n;
    const len = this.obligations.length;
    const holes = this.prog.holeEnvs?.length ?? 0;
    try {
      f();
    } finally {
      this.counter.n = n;
      this.obligations.length = len;
      if (this.prog.holeEnvs) this.prog.holeEnvs.length = holes;
    }
  }
  describe(node: ts.Node): string {
    return nodeText(node);
  }
}

export function extend(env: Env, patch: Partial<Env>): Env {
  return { ...env, ...patch };
}

export function bind(env: Env, sym: ts.Symbol, b: Binding): Env {
  const vars = new Map(env.vars);
  vars.set(sym, b);
  return { ...env, vars };
}

/** Choose a capture-free Lean name for a new local. */
export function freshLocal(env: Env, base: string): { env: Env; name: string } {
  let name = base;
  let i = 1;
  // a «quoted» name takes its suffix inside the quotes
  const suffixed = (k: number) => (base.endsWith("»") ? `${base.slice(0, -1)}_${k}»` : `${base}_${k}`);
  while (env.scope.has(name)) name = suffixed(i++);
  const scope = new Set(env.scope);
  scope.add(name);
  return { env: { ...env, scope }, name };
}
