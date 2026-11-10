import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { TypeRegistry, type VType, type Param, type Field, type TypeEnv, type TParam } from "./types.ts";
import { relLoc, nodeText, subscripted } from "./util.ts";

/** A translated Lean term together with its VTS type. */
export interface Val {
  code: string;
  type: VType;
}

/** The obligation and hypothesis counters of a module context at one point (`ModCtx.replay`). */
export interface Mark {
  n: number;
  hyp: number;
}

/** Information about a pure top-level function. */
export interface FnInfo {
  qname: string;
  name: string;
  /** type parameters (generic function): Lean binders `{T : Type}`, `[DecidableEq T]`, accessors */
  tparams: TParam[];
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

/**
 * Where a DOM event handler is attached: the prop `prop` (`onClick`) of the element `<tag>`, an
 * HTML element when `html` (else an SVG or MathML element of that name: inside `<svg>`, an
 * `<input>` has no value).
 */
export interface DomSite {
  tag: string;
  prop: string;
  html: boolean;
  /** the handler may not update state (a setter or dispatch call is rejected with this message) */
  noUpdates?: string;
  /** set when the handler updates state (a setter or dispatch call on some path) */
  probe?: { updated: boolean };
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
  /** `DomSite.noUpdates` / `DomSite.probe` of the handler's element */
  noUpdates?: string;
  probe?: { updated: boolean };
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
  /**
   * a local function, translated where it is called or attached as a handler, in `env` (that of
   * its creation) extended with the locals declared after it that are initialised there
   * (`closureEnv`); `memo`: a `useCallback` function, which React may keep from an earlier
   * render, so it sees only `env`
   */
  | { k: "closure"; fn: ts.ArrowFunction | ts.FunctionExpression; env: Env; memo?: boolean }
  | { k: "callback"; cb: CallbackInfo }
  | { k: "props" }
  /**
   * the event parameter of the DOM handler `fn`, attached at `site` (its fields are read from the
   * event while `fn` runs; which fields exist depends on the element and the handler prop, not on
   * the parameter's TypeScript type)
   */
  | { k: "event"; leanVar: string; fn: ts.Node; site: DomSite }
  /**
   * a JSX const: translated (obligations checked) at its declaration, bound to the Lean local
   * `code`; `key` is the translation of its element's `key={…}` there (JS evaluates it at the
   * declaration), with the obligations of that translation, for the keys of its siblings
   */
  | { k: "jsx"; node: ts.Expression; env: Env; code: string; key?: Val }
  /**
   * the handle `id` of `const id = setTimeout(…)` / `setInterval(…)` in an effect body, bound once
   * that statement has run (before, `id` is in its temporal dead zone): not a VTS value, only
   * cleared in the effect's cleanup
   */
  | { k: "timer" };

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
  /**
   * Set inside a body that Lean checks for more values than JS gives it (a `for…of` body: any
   * accumulator and element; an array-method callback: any element; a functional update: any
   * state), naming it: `assume(…)` is rejected there (its fact would be a theorem for all of them).
   */
  generalized?: string;
  /**
   * Set only inside a contract that JS never evaluates (the body of an `ensures` lambda, the
   * expression body of a `callbackRequires` lambda, and what they call in place): there
   * `implies(a, b)` reads `b` under the hypothesis `a`.  Every
   * other contract (requires, invariant, assert, assume, a module-level assert, and the
   * callbacks run inside them) is an argument JS evaluates, and `implies` is a function: `b`
   * is evaluated whatever `a` is, so its obligations get no hypothesis from `a` (`prop`).
   */
  ghost?: boolean;
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
  /**
   * What a restricted environment gives access to (a contract, an initial value), for the
   * message when code refers to a local that is not in it.
   */
  limits?: string;
  /** Locals in scope in JS that the translation cannot bind here, with the reason (a timer callback's view of its effect body). */
  unavailable?: Map<ts.Symbol, string>;
  /**
   * The local functions whose bodies are being translated around this point, where they are
   * called or attached as a handler (they are inlined there): one called again inside is a
   * recursive call, which inlining does not support.
   */
  inlining?: ReadonlySet<ts.Node>;
  /**
   * Set inside code that runs while an event handler or effect runs but that VTS translates as a
   * value (an array-method callback, a local helper called for its value, a functional update):
   * why a setter, `dispatch` or parent callback reached there is rejected (render code, where
   * it is unset, gets the render-phase message).
   */
  valueCtx?: string;
}

/** The module of the contract functions and `int`. */
export const SPEC_MODULE = "vreact/spec";
/** This tool's own declarations of vreact/spec (real path). */
/** The real directory of a file (its own path's directory when it cannot be resolved). */
function realDir(f: string): string {
  try {
    return path.dirname(fs.realpathSync(f));
  } catch {
    return path.dirname(path.resolve(f));
  }
}
/** TypeScript's lib directory (real path): where its standard library files are. */
const TS_LIB_DIR = realDir(ts.getDefaultLibFilePath({}));
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

/**
 * The symbol an identifier refers to as a reference.  For the name of a shorthand property
 * `{ x }` this is the variable `x` that the property reads (`getSymbolAtLocation` gives the
 * object literal's property `x`); every scan that collects what code reads (closure checks,
 * initialisation order, declaration order, dependency cones) goes through this.
 */
export function refSymbol(checker: ts.TypeChecker, n: ts.Node): ts.Symbol | undefined {
  if (ts.isIdentifier(n) && ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n) return checker.getShorthandAssignmentValueSymbol(n.parent);
  if (ts.isShorthandPropertyAssignment(n)) return checker.getShorthandAssignmentValueSymbol(n);
  return checker.getSymbolAtLocation(n);
}

/**
 * A type annotation, assertion type or type argument (`x: T`, `e as T`, `f<T>(…)`): erased by
 * TypeScript, so nothing in it is evaluated (the reference scans skip it: a type named like a
 * value, `type Limits = …; const Limits: Limits = …`, resolves to the same merged symbol).
 */
export function isErasedType(n: ts.Node): boolean {
  return ts.isTypeNode(n) && !ts.isExpressionWithTypeArguments(n);
}

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
      moduleNamespaces: new Set(projectFiles.map((sf) => nsOf(sf))),
      // `int` of vreact/spec, also through aliases (`import { type int as I }`, `type Count = int`
      // resolves through typeOfDecl); a project type spelled `int` is the project's
      isSpecInt: (node) => this.specName(ts.isQualifiedName(node.typeName) ? node.typeName.right : node.typeName) === "int",
      isLibType: (node, names) => {
        const s = this.resolve(this.checker.getSymbolAtLocation(ts.isQualifiedName(node.typeName) ? node.typeName.right : node.typeName));
        return !!s && names.includes(s.name) && this.isLibSymbol(s) ? s.name : null;
      },
      isLibSymbol: (s) => this.isLibSymbol(s),
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
    return this.isDefaultLib(sf) || this.tsProgram.isSourceFileFromExternalLibrary(sf) || path.resolve(sf.fileName) === OWN_SPEC;
  }
  /**
   * A file of TypeScript's own standard library (`lib.*.d.ts` in TypeScript's lib directory).
   * `Program.isSourceFileDefaultLibrary` alone also answers true for any declaration file with
   * `/// <reference no-default-lib="true"/>`, which a project file could use to pass as the library.
   */
  isDefaultLib(sf: ts.SourceFile): boolean {
    return this.tsProgram.isSourceFileDefaultLibrary(sf) && realDir(sf.fileName) === TS_LIB_DIR;
  }
  isReactFile(sf: ts.SourceFile): boolean {
    return this.isLibraryFile(sf) && REACT_FILE_RE.test(sf.fileName);
  }
  /**
   * A declaration of JavaScript's standard library — a lib type or value (`ReadonlyArray`,
   * `ReadonlyMap`, `Set`, the `Map` constructor, `Array.from`, a method of one of them), through
   * import aliases: declared in TypeScript's default library, and nowhere but in library files
   * (an installed package may add to it, e.g. @types/node to `Array`; a project declaration
   * spelled like one, or merged into one, is the project's).
   */
  isLibSymbol(s0: ts.Symbol | undefined): boolean {
    const s = this.resolve(s0);
    return !!s && this.declaredIn(s, (f) => this.isLibraryFile(f)) && s.declarations!.some((d) => this.isDefaultLib(d.getSourceFile()));
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
    const s = refSymbol(this.checker, n);
    if (!s) return false;
    if (name === "undefined") return this.checker.isUndefinedSymbol(s);
    return !(s.flags & ts.SymbolFlags.Alias) && this.declaredIn(s, (f) => this.isLibraryFile(f));
  }
  /** The name of the vreact/spec declaration (function or `int`) that `n` refers to, through import aliases. */
  specName(n: ts.Node): string | null {
    if (!ts.isIdentifier(n)) return null;
    const s = this.resolve(refSymbol(this.checker, n));
    return s && this.declaredIn(s, (f) => this.specFiles.has(f)) ? s.name : null;
  }
  /** The name of the React declaration (hook, type) that `n` refers to, through import aliases. */
  reactName(n: ts.Node): string | null {
    if (!ts.isIdentifier(n)) return null;
    const s = this.resolve(refSymbol(this.checker, n));
    return s && this.declaredIn(s, (f) => this.isReactFile(f)) ? s.name : null;
  }
  /**
   * Is `id` bound by an import declaration (`import { x }`, `import * as x`, `import x`)?  Not a
   * UMD global (`export as namespace React` in React's types, usable without an import under
   * "allowUmdGlobalAccess"), which a module bundle does not define.
   */
  isImportBinding(id: ts.Identifier): boolean {
    const s = refSymbol(this.checker, id);
    const ds = s && s.flags & ts.SymbolFlags.Alias ? s.declarations : undefined;
    return !!ds?.length && ds.every((d) => ts.isImportSpecifier(d) || ts.isNamespaceImport(d) || ts.isImportClause(d));
  }
  /**
   * The declaration a reference resolves to (through shorthand properties and import aliases):
   * what the scans of module.ts, component.ts and synth.ts follow.
   */
  refDecl(n: ts.Node): ts.Declaration | undefined {
    const s = this.resolve(refSymbol(this.checker, n));
    return s?.valueDeclaration ?? s?.declarations?.[0];
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
  /**
   * The tactic of the obligations emitted now (`ob`): `vreact_auto`, except while a
   * module-level fact's statement is translated, whose obligations (an index, a divisor, a
   * precondition) first unfold the `@opaque` constants the fact mentions (translateFact).
   */
  obTactic = "vreact_auto";
  /** Emit a proof obligation discharged by `vreact_auto` (`obTactic`), tagged with a source
   * marker; `vreact_ob` gives it its own heartbeat budget (VReact/Budget.lean). */
  ob(node: ts.Node, kind: string, desc: string, tactic = this.obTactic): string {
    const id = ++this.counter.n;
    const sf = node.getSourceFile();
    const { line } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    this.obligations.push({ id, kind, desc, where: relLoc(node, this.prog.root), file: sf.fileName, line: line + 1 });
    return `(/-⟦ob${id}⟧-/ by vreact_ob ${tactic})`;
  }
  obCount(): number {
    return this.obligations.length;
  }
  /** The obligation and hypothesis counters at this point of the translation (for `replay`). */
  mark(): Mark {
    return { n: this.counter.n, hyp: this.hyp };
  }
  /**
   * Translate again, from the counters at `from`, what was translated between the marks `from`
   * and `to`: the translation is deterministic, so this gives the same text — the same
   * obligation ids (`/-⟦obN⟧-/`) and hypothesis names — and the obligations in it are copies of
   * those registered then (one obligation may have several copies in the generated Lean: it is
   * proved only if every copy is), which are not registered again.  `f` may translate other
   * things around it (a term built from the same pieces) as long as it makes the same calls.
   * Afterwards the counters are as before the replay.
   */
  replay<R>(from: Mark, to: Mark, f: () => R): R {
    const n = this.counter.n;
    const hyp = this.hyp;
    const len = this.obligations.length;
    const holes = this.prog.holeEnvs?.length ?? 0;
    this.counter.n = from.n;
    this.hyp = from.hyp;
    try {
      const r = f();
      if (this.counter.n !== to.n || this.hyp !== to.hyp) {
        throw new Error(`internal error: a replayed translation did not repeat itself (obligation counter ${from.n}→${to.n}, replayed →${this.counter.n}; hypotheses ${from.hyp}→${to.hyp}, replayed →${this.hyp})`);
      }
      return r;
    } finally {
      this.counter.n = n;
      this.hyp = hyp;
      this.obligations.length = len;
      if (this.prog.holeEnvs) this.prog.holeEnvs.length = holes;
    }
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
