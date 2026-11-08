import ts from "typescript";
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

/** Per-program translation context. */
export class Program {
  checker: ts.TypeChecker;
  reg = new TypeRegistry();
  globals = new Map<ts.Node, Global>();
  root: string;
  typeEnv: TypeEnv;
  modNs = new Map<string, string>();
  /** set by `vreact synth`: every translation of a `hole<T>()` kept in the output, with its environment (narrowing) */
  holeEnvs?: HoleEnv[];
  constructor(checker: ts.TypeChecker, root: string, nsOf: (sf: ts.SourceFile) => string, program: ts.Program) {
    this.checker = checker;
    this.root = root;
    this.typeEnv = {
      checker,
      reg: this.reg,
      nsOf,
      fileKind: (sf) =>
        program.isSourceFileDefaultLibrary(sf) ? "lib" : program.isSourceFileFromExternalLibrary(sf) || (sf.isDeclarationFile && /[\\/]node_modules[\\/]/.test(sf.fileName)) ? "external" : "user",
      isSpecInt: (node) => {
        if (node.typeName.getText() !== "int") return false;
        let sym = checker.getSymbolAtLocation(node.typeName);
        if (!sym) return false;
        if (sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym);
        const d = sym.declarations?.[0];
        return !!d && /vreact[\\/](spec|lib)|vreact-spec/.test(d.getSourceFile().fileName);
      },
    };
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
