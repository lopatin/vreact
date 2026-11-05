/**
 * React components → instances of the Lean model `VReact.Component`.
 *
 *   props            ↦ structure Props (data) + structure Cb (callbacks with contracts)
 *   useState/Reducer ↦ fields of structure State
 *   requires(…)      ↦ pre,   invariant(…) ↦ inv,   initial values ↦ init
 *   JSX              ↦ a proof-carrying VNode tree (handlers, child preconditions, keys)
 *   useEffect        ↦ VReact.Effect with robust outcomes
 */
import ts from "typescript";
import { T, type VType, type Param, type Field, leanType, showType, typeOfNode } from "./types.ts";
import { type Env, ModCtx, type CompCtx, type CompInfo, type StateVar, type FnInfo, type Binding, bind, freshLocal } from "./ctx.ts";
import { expr, prop, block, branch, handlerFn, checkDeps, hookName, specFn, symbolOf, bindParam, type BlockCtx, typeOf, valueBlock, lambda, outcome } from "./translate.ts";
import { fail, leanField, leanIdent, leanStr, jsStr, paren, nodeText, indent } from "./util.ts";

const CONTINUOUS = new Set(["drag", "dragenter", "dragexit", "dragleave", "dragover", "mousemove", "mouseout", "mouseover", "pointermove", "pointerout", "pointerover", "scroll", "toggle", "touchmove", "wheel", "mouseenter", "mouseleave", "pointerenter", "pointerleave"]);
const EVENT_RENAME: Record<string, string> = { doubleclick: "dblclick" };

const RESERVED = ["E", "σ", "τ", "κ", "hpre", "hinv", "props", "ev", "acc"];

export function baseEnv(m: ModCtx): Env {
  return { m, vars: new Map(), narrow: new Map(), scope: new Set(RESERVED), mode: "code" };
}

/** Collect the signature of a component (props split into data and callbacks). */
export function compSignature(fn: ts.FunctionDeclaration, ns: string, module: string, m: ModCtx, trusted: boolean): CompInfo {
  const name = fn.name!.text;
  const p = fn.parameters[0];
  if (fn.parameters.length > 1) fail(fn.parameters[1], "components take a single props parameter");
  let data: Field[] = [];
  const callbacks: { name: string; params: Param[] }[] = [];
  let propsType: VType | null = null;
  if (p) {
    if (!p.type) fail(p, "annotate the props parameter type");
    propsType = typeOfNode(p.type, m.prog.typeEnv, name + "Props");
    if (propsType.k !== "rec") fail(p, "props must be an object type");
    for (const f of m.reg.rec(propsType)) {
      if (f.type.k === "fn") {
        if (f.type.ret.k !== "void") fail(p, `callback ${f.name} must return void`);
        callbacks.push({ name: f.name, params: f.type.params });
      } else if (f.type.k === "opt" && f.type.elem.k === "fn") {
        fail(p, `optional callback ${f.name} is not supported: make it required`);
      } else if (f.type.k === "node") {
        fail(p, `${f.name}: ReactNode props (children) are not supported yet`);
      } else data.push(f);
    }
  }
  return { name, ns: `${ns}.${name}`, module, data, callbacks, decl: fn, trusted, propsType };
}

interface Prepass {
  pre: string[];
  inv: string[];
  stateVars: StateVar[];
  inits: string[];
  contracts: Map<string, { binders: string[]; prop: string }>;
  renderStmts: ts.Statement[];
  /** env with props bound (for pre / contracts / init) */
  propsEnv: Env;
}

/** Translate one component into its Lean namespace. */
export function translateComponent(fn: ts.FunctionDeclaration, info: CompInfo, m: ModCtx): string {
  const ns = info.ns;
  const comp: CompCtx = { info, stateType: `${ns}.State`, stateVars: [], propsVar: "props", cbVar: "κ", snap: "σ", invName: `${ns}.inv` };
  let env: Env = { ...baseEnv(m), comp };
  // props parameter
  const p = fn.parameters[0];
  if (p) {
    if (ts.isIdentifier(p.name)) env = bind(env, symbolOf(env, p.name)!, { k: "props" });
    else if (ts.isObjectBindingPattern(p.name)) {
      for (const el of p.name.elements) {
        if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) fail(el, "only simple props destructuring { a, b } is supported");
        const fname = el.propertyName ? el.propertyName.getText() : el.name.text;
        const d = info.data.find((f) => f.name === fname);
        const cb = info.callbacks.find((c) => c.name === fname);
        const sym = symbolOf(env, el.name)!;
        if (d) env = bind(env, sym, { k: "val", code: `props.${leanField(fname)}`, type: d.type });
        else if (cb) env = bind(env, sym, { k: "callback", cb });
        else fail(el, `no prop ${fname}`);
      }
    } else fail(p, "unsupported props pattern");
  }
  const body = fn.body;
  if (!body) fail(fn, "component without body");
  const pp = prepass(body.statements, env, comp, m);
  comp.stateVars = pp.stateVars;

  // ---- declarations ----
  let out = `namespace ${info.name}\n\n`;
  out += `/-- Props (data part) of ${info.name}. -/\nstructure Props where\n${info.data.map((f) => `  ${leanField(f.name)} : ${leanType(f.type)}`).join("\n")}\n\n`;
  out += `/-- Callback props of ${info.name}; each carries its contract. -/\nstructure Cb (props : Props) (E : Type) : Type where\n`;
  for (const cb of info.callbacks) {
    const c = pp.contracts.get(cb.name);
    const binders = cb.params.map((q, i) => `(${c ? c.binders[i] : leanIdent(q.name)} : ${leanType(q.type)})`).join(" → ");
    const pre = c ? c.prop : "True";
    out += `  ${leanField(cb.name)} : ${binders ? binders + " → " : ""}(${pre}) → E\n`;
  }
  out += `\n/-- Hook state of ${info.name} (one field per useState/useReducer). -/\nstructure State where\n${pp.stateVars.map((s) => `  ${leanField(s.field)} : ${leanType(s.type)}`).join("\n")}\n\n`;
  out += `@[vreact_simp] def pre (props : Props) : Prop :=\n  ${pp.pre.length ? pp.pre.join(" ∧\n  ") : "True"}\n\n`;
  const stateLets = pp.stateVars.map((s) => `let ${leanIdent(s.name)} := σ.${leanField(s.field)}; `).join("");
  out += `@[vreact_simp] def inv (props : Props) (σ : State) : Prop :=\n  ${pp.inv.length ? stateLets + "\n  " + pp.inv.join(" ∧\n  ") : "True"}\n\n`;
  out += `@[vreact_simp] def init (props : Props) (hpre : pre props) : State :=\n  State.mk${pp.inits.map((x) => " " + paren(x)).join("")}\n\n`;
  const invNode = fn.name!;
  if (info.trusted) {
    out += `axiom init_inv : ∀ (props : Props) (hpre : pre props), inv props (init props hpre)\n`;
    out += `axiom stable : ∀ (props props' : Props) (σ : State), inv props σ → pre props' → inv props' σ\n\n`;
  } else {
    out += `theorem init_inv : ∀ (props : Props) (hpre : pre props), inv props (init props hpre) :=\n  ${m.ob(invNode, "init-invariant", `${info.name}: initial state satisfies the invariant`)}\n\n`;
    out += `theorem stable : ∀ (props props' : Props) (σ : State), inv props σ → pre props' → inv props' σ :=\n  ${m.ob(invNode, "props-stability", `${info.name}: invariant survives a re-render with new props (state is preserved)`)}\n\n`;
  }
  out += `abbrev spec : VReact.Spec :=\n  { name := ${leanStr(info.name)}, D := Props, Cb := Cb, S := State, pre := pre, inv := inv,\n    init := init, init_inv := init_inv, stable := stable }\n\n`;

  // ---- render ----
  const sig = `def render {E : Type} (props : Props) (κ : Cb props E) (σ : State) (hpre : pre props) (hinv : inv props σ) :\n    VReact.VNode State E (inv props) σ`;
  if (info.trusted) {
    out += `axiom renderTrusted {E : Type} (props : Props) (κ : Cb props E) (σ : State) (hpre : pre props) (hinv : inv props σ) :\n    VReact.VNode State E (inv props) σ\n`;
    out += `${sig} :=\n  renderTrusted props κ σ hpre hinv\n\n`;
  } else {
    let renv: Env = env;
    let lets = "";
    for (const sv of pp.stateVars) {
      lets += `let ${leanIdent(sv.name)} := σ.${leanField(sv.field)};\n  `;
    }
    renv = bindStateVars(renv, body.statements, pp.stateVars);
    const effects: string[] = [];
    const bc: BlockCtx = {
      kind: "render",
      fnNode: fn,
      onReturn: (e, env2) => {
        if (!e) fail(fn, "components must return JSX or null");
        const node = jsxNode(e, env2);
        return effects.length ? `(VReact.VNode.withEffects [${effects.join(",\n  ")}]\n  ${paren(node)})` : node;
      },
    };
    (bc as BlockCtx & { onEffect?: (c: ts.CallExpression, env: Env) => void }).onEffect = (c, env2) => {
      effects.push(effectCode(c, env2, info));
    };
    const renderBody = renderBlock(pp.renderStmts, renv, bc);
    out += `${sig} :=\n  ${lets}${renderBody}\n\n`;
  }
  out += `def component : VReact.Component spec := ⟨fun d cb s hpre hinv => render d cb s hpre hinv⟩\n\n`;
  out += `end ${info.name}\n`;
  return out;
}

function bindStateVars(env: Env, stmts: readonly ts.Statement[], svs: StateVar[]): Env {
  let e = env;
  for (const s of stmts) {
    if (!ts.isVariableStatement(s)) continue;
    for (const d of s.declarationList.declarations) {
      if (!ts.isArrayBindingPattern(d.name) || !d.initializer || !ts.isCallExpression(d.initializer)) continue;
      const h = hookName(e, d.initializer.expression);
      if (h !== "useState" && h !== "useReducer") continue;
      const [a, b] = d.name.elements;
      const sv = svs.find((x) => ts.isBindingElement(a) && ts.isIdentifier(a.name) && x.name === a.name.text)!;
      if (ts.isBindingElement(a) && ts.isIdentifier(a.name)) {
        e = bind(e, symbolOf(e, a.name)!, { k: "val", code: leanIdent(sv.name), type: sv.type });
        const sc = new Set(e.scope);
        sc.add(leanIdent(sv.name));
        e = { ...e, scope: sc };
      }
      if (b && ts.isBindingElement(b) && ts.isIdentifier(b.name)) {
        e = bind(e, symbolOf(e, b.name)!, h === "useState" ? { k: "setter", sv } : { k: "dispatch", sv });
      }
    }
  }
  return e;
}

/** Render statements: like `block`, plus useEffect handling. */
function renderBlock(stmts: ts.Statement[], env: Env, bc: BlockCtx): string {
  const onEffect = (bc as BlockCtx & { onEffect?: (c: ts.CallExpression, env: Env) => void }).onEffect!;
  // peel effects off at top level (they are hooks: unconditional, before returns)
  const rest: ts.Statement[] = [];
  const run = (i: number, e: Env): string => {
    if (i >= stmts.length) fail(bc.fnNode, "component must return");
    const s = stmts[i];
    if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && hookName(e, s.expression.expression) === "useEffect") {
      onEffect(s.expression, e);
      return run(i + 1, e);
    }
    // translate this statement with a continuation that resumes the scan
    return block([s], 0, e, bc, (e2) => run(i + 1, e2));
  };
  return run(0, env);
}

function prepass(stmts: readonly ts.Statement[], env: Env, comp: CompCtx, m: ModCtx): Prepass {
  const pp: Prepass = { pre: [], inv: [], stateVars: [], inits: [], contracts: new Map(), renderStmts: [], propsEnv: env };
  let sawNonHook = false;
  let stateEnv: Env = env; // props + state (as σ.field) for invariants
  for (const s of stmts) {
    if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression)) {
      const c = s.expression;
      const sf = specFn(env, c.expression);
      if (sf === "requires") {
        pp.pre.push(prop(c.arguments[0], env));
        continue;
      }
      if (sf === "invariant") {
        pp.inv.push(prop(c.arguments[0], stateEnv));
        continue;
      }
      if (sf === "callbackRequires") {
        const cbE = c.arguments[0];
        const name = ts.isPropertyAccessExpression(cbE) ? cbE.name.text : ts.isIdentifier(cbE) ? cbE.text : null;
        const cb = comp.info.callbacks.find((x) => x.name === name);
        if (!cb) fail(cbE, "callbackRequires expects a callback prop");
        const lam = c.arguments[1];
        if (!lam || !(ts.isArrowFunction(lam) || ts.isFunctionExpression(lam))) fail(c, "callbackRequires(cb, (args) => condition)");
        const l = lambda(lam, env, cb.params.map((p) => p.type), T.bool);
        pp.contracts.set(cb.name, { binders: l.binders, prop: `${paren(l.body.code)} = true` });
        continue;
      }
      if (sf) fail(c, `${sf}(…) is not allowed in a component body`);
      const h = hookName(env, c.expression);
      if (h === "useEffect" || h === "useLayoutEffect") {
        if (sawNonHook) fail(c, "hooks must run unconditionally before any early return (Rules of Hooks)");
        pp.renderStmts.push(s);
        continue;
      }
    }
    if (ts.isVariableStatement(s)) {
      const d = s.declarationList.declarations[0];
      if (d && d.initializer && ts.isCallExpression(d.initializer)) {
        const h = hookName(env, d.initializer.expression);
        if (h === "useState" || h === "useReducer") {
          if (sawNonHook) fail(d, "hooks must run unconditionally before any early return (Rules of Hooks)");
          if (s.declarationList.declarations.length !== 1) fail(s, "one hook per declaration");
          const sv = stateVar(d, h, env, m, pp);
          pp.stateVars.push(sv);
          const a = (d.name as ts.ArrayBindingPattern).elements[0] as ts.BindingElement;
          stateEnv = bind(stateEnv, symbolOf(env, a.name)!, { k: "val", code: leanIdent(sv.name), type: sv.type });
          continue;
        }
        if (h === "useRef" || h === "useContext" || h === "useLayoutEffect" || h === "useSyncExternalStore" || h === "useTransition" || h === "useDeferredValue" || h === "useId" || h === "useImperativeHandle") {
          fail(d, `${h} is not modelled in VTS yet`);
        }
      }
    }
    if (ts.isIfStatement(s) || ts.isReturnStatement(s)) sawNonHook = true;
    pp.renderStmts.push(s);
  }
  return pp;
}

function stateVar(d: ts.VariableDeclaration, h: string, env: Env, m: ModCtx, pp: Prepass): StateVar {
  if (!ts.isArrayBindingPattern(d.name) || d.name.elements.length < 1) fail(d, `use const [value, setValue] = ${h}(…)`);
  const a = d.name.elements[0];
  if (!ts.isBindingElement(a) || !ts.isIdentifier(a.name)) fail(d, "state variable must be an identifier");
  const name = a.name.text;
  const c = d.initializer as ts.CallExpression;
  if (h === "useState") {
    let t: VType | undefined = c.typeArguments?.[0] ? typeOfNode(c.typeArguments[0], m.prog.typeEnv, name[0].toUpperCase() + name.slice(1)) : undefined;
    const init = c.arguments[0];
    if (!init) fail(c, "useState needs an initial value");
    let v;
    const ii = ts.isParenthesizedExpression(init) ? init.expression : init;
    if (ts.isArrowFunction(ii) && ii.parameters.length === 0) {
      v = ts.isBlock(ii.body) ? valueBlock(ii.body.statements, env, t, ii) : expr(ii.body, env, t);
    } else v = expr(init, env, t);
    t = t ?? v.type;
    pp.inits.push(v.code);
    return { name, field: name, type: t };
  }
  // useReducer(reducer, initialArg, init?)
  const rId = c.arguments[0];
  if (!rId || !ts.isIdentifier(rId)) fail(c, "useReducer(reducer, initial): reducer must be a top-level function");
  let sym = env.m.checker.getSymbolAtLocation(rId);
  if (sym && sym.flags & ts.SymbolFlags.Alias) sym = env.m.checker.getAliasedSymbol(sym);
  const g = sym?.declarations?.[0] ? m.prog.globals.get(sym.declarations[0]) : undefined;
  if (!g || g.k !== "fn") fail(rId, "reducer must be a verified top-level function");
  const r = g.info;
  if (r.params.length !== 2) fail(rId, "a reducer takes (state, action)");
  if (r.hasPre) fail(rId, "reducers must be total (no requires): React may call them on any queued state");
  const st = r.params[0].type;
  m.deps.add(r.qname);
  let initCode: string;
  if (c.arguments[2]) {
    const initFn = c.arguments[2];
    if (!ts.isIdentifier(initFn)) fail(initFn, "init must be a top-level function");
    const call = ts.factory.createCallExpression(initFn, undefined, [c.arguments[1]]);
    fail(initFn, "useReducer's third (init) argument is not supported; compute the initial state in the second argument");
  } else {
    initCode = expr(c.arguments[1], env, st).code;
  }
  pp.inits.push(initCode!);
  return { name, field: name, type: st, reducer: r, actionType: r.params[1].type };
}

/* ───────────────────────────── effects ───────────────────────────── */

function effectCode(c: ts.CallExpression, env: Env, info: CompInfo): string {
  const m = env.m;
  const fn = c.arguments[0];
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length) fail(c, "useEffect(() => { … }, [deps])");
  if (fn.modifiers?.some((x) => x.kind === ts.SyntaxKind.AsyncKeyword)) fail(fn, "async effects are not supported");
  checkDeps(fn, c.arguments[1], env, "useEffect");
  // deps
  let deps = "none";
  if (c.arguments[1] && ts.isArrayLiteralExpression(c.arguments[1])) {
    const ds = c.arguments[1].elements.map((d) => {
      const v = expr(d, env);
      switch (v.type.k) {
        case "int":
          return `VReact.DepVal.int ${paren(v.code)}`;
        case "str":
          return `VReact.DepVal.str ${paren(v.code)}`;
        case "bool":
          return `VReact.DepVal.bool ${paren(v.code)}`;
        case "enum":
          return `VReact.DepVal.str (VReact.JS.str ${paren(v.code)})`;
        default:
          return `VReact.DepVal.obj`;
      }
    });
    deps = `some [${ds.join(", ")}]`;
  }
  // split the body into: synchronous statements, timer registrations (tasks), cleanup
  const stmts = ts.isBlock(fn.body) ? [...fn.body.statements] : [ts.factory.createExpressionStatement(fn.body)];
  const tasks: string[] = [];
  const sync: ts.Statement[] = [];
  const timerCb = (e: ts.Expression): ts.Expression | null => {
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && ["setInterval", "setTimeout"].includes(e.expression.text)) return e.arguments[0];
    return null;
  };
  for (const s of stmts) {
    if (ts.isReturnStatement(s)) {
      // cleanup: may not touch state
      if (s.expression && containsSetter(s.expression, env)) fail(s, "effect cleanups may not update state");
      continue;
    }
    let cb: ts.Expression | null = null;
    if (ts.isExpressionStatement(s)) cb = timerCb(s.expression);
    if (ts.isVariableStatement(s) && s.declarationList.declarations.length === 1 && s.declarationList.declarations[0].initializer) {
      cb = timerCb(s.declarationList.declarations[0].initializer!);
    }
    if (cb) {
      const h = handlerFn(cb, env, "robust", []);
      tasks.push(`(fun _ => ${h.code})`);
      continue;
    }
    sync.push(s);
  }
  // translate the synchronous part as a robust handler body
  const fake = ts.factory.createArrowFunction(undefined, undefined, [], undefined, undefined, ts.factory.createBlock(sync));
  let setup: string;
  if (sync.length === 0) setup = `(VReact.Outcome.mk (S := ${info.ns}.State) (E := E) [] none)`;
  else {
    // translate statements directly (synthetic nodes have no positions; use the original statements)
    const acc = { kind: "robust" as const, updates: [], emit: null, eventVar: null };
    const e1: Env = { ...env, handler: acc, curState: undefined };
    const done = (e3: Env) => outcome(e3.handler!, env.comp!);
    setup = block(sync, 0, e1, { kind: "handler", fnNode: fn, onDone: done }, done);
  }
  void fake;
  const okSetup = m.ob(c, "effect-robust", `effect at ${nodeText(c, 40)} preserves the invariant of ${info.name} from any state (effects may run with stale snapshots)`);
  const okTasks = tasks.length
    ? m.ob(c, "effect-robust", `timer callbacks of the effect preserve the invariant of ${info.name} from any state`)
    : `(by simp)`;
  return `(VReact.Effect.mk (S := ${info.ns}.State) (E := E) (inv := ${info.ns}.inv props) (${deps}) ${paren(setup)} ${okSetup} rfl\n     [${tasks.join(", ")}] ${okTasks})`;
}

function containsSetter(n: ts.Node, env: Env): boolean {
  let found = false;
  const visit = (x: ts.Node) => {
    if (ts.isCallExpression(x) && ts.isIdentifier(x.expression)) {
      const s = symbolOf(env, x.expression);
      const b = s ? env.vars.get(s) : undefined;
      if (b && (b.k === "setter" || b.k === "dispatch")) found = true;
    }
    ts.forEachChild(x, visit);
  };
  visit(n);
  return found;
}

/* ───────────────────────────── JSX ───────────────────────────── */

function isJsx(e: ts.Node): boolean {
  return ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e) || ts.isJsxFragment(e);
}

/** A VNode term for a JSX-valued expression. */
export function jsxNode(e0: ts.Expression, env: Env): string {
  const e = ts.isParenthesizedExpression(e0) ? e0.expression : e0;
  if (ts.isParenthesizedExpression(e)) return jsxNode(e.expression, env);
  if (e.kind === ts.SyntaxKind.NullKeyword || (ts.isIdentifier(e) && e.text === "undefined") || e.kind === ts.SyntaxKind.FalseKeyword) return "VReact.VNode.empty";
  if (ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) return element(e, env);
  if (ts.isJsxFragment(e)) return `(VReact.VNode.elem "fragment" [] [] ${children(e.children, env)})`;
  if (ts.isConditionalExpression(e)) return branch(e.condition, env, (e1) => jsxNode(e.whenTrue, e1), (e2) => jsxNode(e.whenFalse, e2));
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) {
    return branch(e.left, env, (e1) => jsxNode(e.right, e1), () => "VReact.VNode.empty");
  }
  if (ts.isIdentifier(e)) {
    const s = symbolOf(env, e);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "jsx") return jsxNode(b.node, { ...b.env, scope: env.scope });
  }
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.name.text === "map") return keyedMap(e, env);
  // a value rendered as text
  const v = expr(e, env);
  switch (v.type.k) {
    case "str":
      return `(VReact.VNode.text ${paren(v.code)})`;
    case "int":
    case "num":
    case "enum":
      return `(VReact.VNode.text (VReact.JS.str ${paren(v.code)}))`;
    case "bool":
      return "VReact.VNode.empty"; // React renders nothing for booleans
    case "opt":
      if (v.type.elem.k === "str") return `(match ${v.code} with | some s => VReact.VNode.text s | none => VReact.VNode.empty)`;
      if (["int", "enum"].includes(v.type.elem.k)) return `(match ${v.code} with | some s => VReact.VNode.text (VReact.JS.str s) | none => VReact.VNode.empty)`;
      fail(e, `cannot render ${showType(v.type)}`);
    default:
      fail(e, `cannot render a value of type ${showType(v.type)} (arrays need .map with keys)`);
  }
}

function children(cs: ts.NodeArray<ts.JsxChild>, env: Env): string {
  const items: string[] = [];
  for (const c of cs) {
    if (ts.isJsxText(c)) {
      const t = jsxText(c.text);
      if (t) items.push(`(VReact.VNode.text ${jsStr(t)})`);
      continue;
    }
    if (ts.isJsxExpression(c)) {
      if (!c.expression) continue;
      if (c.dotDotDotToken) fail(c, "spread children are not supported");
      items.push(jsxNode(c.expression, env));
      continue;
    }
    items.push(jsxNode(c as ts.Expression, env));
  }
  return items.length ? `(VReact.VList.ofList [\n    ${items.map((i) => indent(i, 2).trimStart()).join(",\n    ")}])` : "VReact.VList.nil";
}

/** React's JSX whitespace rules. */
function jsxText(raw: string): string {
  const lines = raw.split(/\r\n|\n|\r/);
  if (lines.length === 1) return raw;
  const parts: string[] = [];
  lines.forEach((l, i) => {
    let t = l;
    if (i !== 0) t = t.replace(/^[ \t]+/, "");
    if (i !== lines.length - 1) t = t.replace(/[ \t]+$/, "");
    if (t) parts.push(t);
  });
  return parts.join(" ");
}

function attrs(e: ts.JsxElement | ts.JsxSelfClosingElement): ts.NodeArray<ts.JsxAttributeLike> {
  return ts.isJsxElement(e) ? e.openingElement.attributes.properties : e.attributes.properties;
}

function element(e: ts.JsxElement | ts.JsxSelfClosingElement, env: Env): string {
  const tagNode = ts.isJsxElement(e) ? e.openingElement.tagName : e.tagName;
  const tag = tagNode.getText();
  const kids = ts.isJsxElement(e) ? e.children : undefined;
  if (/^[a-z]/.test(tag)) return intrinsic(tag, e, kids, env);
  return componentElement(tagNode, e, kids, env);
}

function attrValue(a: ts.JsxAttribute): ts.Expression | null {
  if (!a.initializer) return null;
  if (ts.isStringLiteral(a.initializer)) return a.initializer;
  if (ts.isJsxExpression(a.initializer)) {
    if (!a.initializer.expression) fail(a, "empty attribute expression");
    return a.initializer.expression;
  }
  fail(a, "unsupported attribute value");
}

/**
 * Event bubbling: one DOM event runs the handlers of the target and of all its
 * ancestors.  The model runs exactly one handler per event, so VTS rejects
 * layouts where an event could reach two handlers of the same component tree:
 * an element with `onX` containing a descendant with `onX` or a user component,
 * and a submit button with `onClick` inside a `<form onSubmit>`.
 */
function checkBubbling(e: ts.JsxElement | ts.JsxSelfClosingElement, events: string[], env: Env) {
  if (!events.length || !ts.isJsxElement(e)) return;
  const isSubmitForm = e.openingElement.tagName.getText() === "form" && events.includes("onSubmit");
  const visit = (n: ts.Node) => {
    if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n)) {
      const tag = (ts.isJsxElement(n) ? n.openingElement.tagName : n.tagName).getText();
      const as = attrs(n).filter(ts.isJsxAttribute).map((a) => a.name.getText());
      if (/^[A-Z]/.test(tag)) fail(n, `<${tag}> is nested inside an element with ${events.join("/")}: its events would bubble into a second handler (move the handler, or the component, out)`);
      const clash = as.filter((x) => events.includes(x));
      if (clash.length) fail(n, `${clash.join(", ")} on <${tag}> is nested inside an element with the same handler: one event would run both (event bubbling)`);
      if (isSubmitForm && tag === "button" && as.includes("onClick")) {
        const typeAttr = attrs(n).find((a) => ts.isJsxAttribute(a) && a.name.getText() === "type") as ts.JsxAttribute | undefined;
        const t = typeAttr?.initializer && ts.isStringLiteral(typeAttr.initializer) ? typeAttr.initializer.text : "submit";
        if (t === "submit") fail(n, `a submit button with onClick inside <form onSubmit>: one click runs both handlers (use type="button", or put the logic in onSubmit)`);
      }
    }
    ts.forEachChild(n, visit);
  };
  for (const c of e.children) visit(c);
}

function intrinsic(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  checkBubbling(e, attrs(e).filter(ts.isJsxAttribute).map((a) => a.name.getText()).filter((n) => /^on[A-Z]/.test(n)), env);
  const as: string[] = [];
  const hs: string[] = [];
  for (const a of attrs(e)) {
    if (ts.isJsxSpreadAttribute(a)) fail(a, "spread attributes are not supported");
    const name = a.name.getText();
    if (name === "key") continue;
    if (name === "ref" || name === "dangerouslySetInnerHTML") fail(a, `${name} is not supported in VTS`);
    const val = attrValue(a);
    if (/^on[A-Z]/.test(name)) {
      if (!val) fail(a, "handler attribute needs a value");
      let ev = name.slice(2).toLowerCase();
      ev = EVENT_RENAME[ev] ?? ev;
      const continuous = CONTINUOUS.has(ev);
      const h = handlerFn(val, env, continuous ? "robust" : "discrete", "event");
      const run = `(fun ${h.params[0] ?? "_"} => ${h.code})`;
      if (continuous) {
        const ok = m.ob(a, "handler-robust", `${name} handler on <${tag}> (continuous event) preserves the invariant of ${env.comp!.info.name} from any state`);
        hs.push(`(VReact.Handler.continuous ${leanStr(ev)} ${run} ${ok} (by intros; rfl))`);
      } else {
        const ok = m.ob(a, "handler", `${name} handler on <${tag}> preserves the invariant of ${env.comp!.info.name}`);
        hs.push(`(VReact.Handler.discrete ${leanStr(ev)} ${run} ${ok} (by decide))`);
      }
      continue;
    }
    if (name === "style") fail(a, "inline style objects are not supported: use className");
    if (!val) {
      as.push(`⟨${leanStr(name)}, VReact.AttrVal.bool true⟩`);
      continue;
    }
    if (ts.isStringLiteral(val)) {
      as.push(`⟨${leanStr(name)}, VReact.AttrVal.str ${jsStr(val.text)}⟩`);
      continue;
    }
    const v = expr(val, env);
    let av: string;
    switch (v.type.k) {
      case "str":
        av = `VReact.AttrVal.str ${paren(v.code)}`;
        break;
      case "int":
        av = `VReact.AttrVal.int ${paren(v.code)}`;
        break;
      case "bool":
        av = `VReact.AttrVal.bool ${paren(v.code)}`;
        break;
      case "num":
        av = `VReact.AttrVal.num ${paren(v.code)}`;
        break;
      case "enum":
        av = `VReact.AttrVal.str (VReact.JS.str ${paren(v.code)})`;
        break;
      case "opt":
        if (v.type.elem.k === "str") {
          av = `(match ${v.code} with | some s => VReact.AttrVal.str s | none => VReact.AttrVal.none)`;
          break;
        }
        fail(val, `attribute of type ${showType(v.type)} not supported`);
      default:
        fail(val, `attribute of type ${showType(v.type)} not supported`);
    }
    as.push(`⟨${leanStr(name)}, ${av}⟩`);
  }
  const ch = kids ? children(kids, env) : "VReact.VList.nil";
  return `(VReact.VNode.elem ${leanStr(tag)} [${as.join(", ")}]\n  [${hs.join(",\n   ")}]\n  ${ch})`;
}

function componentElement(tagNode: ts.JsxTagNameExpression, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  let sym = m.checker.getSymbolAtLocation(tagNode);
  if (sym && sym.flags & ts.SymbolFlags.Alias) sym = m.checker.getAliasedSymbol(sym);
  const g = sym?.declarations?.[0] ? m.prog.globals.get(sym.declarations[0]) : undefined;
  if (!g || g.k !== "comp") fail(tagNode, `<${tagNode.getText()}> is not a verified component (declare it in a VTS module, or mark it @trusted)`);
  const info = g.info;
  if (kids && kids.some((k) => !(ts.isJsxText(k) && !jsxText(k.text)))) fail(e, "children of user components are not supported yet");
  const given = new Map<string, ts.JsxAttribute>();
  for (const a of attrs(e)) {
    if (ts.isJsxSpreadAttribute(a)) fail(a, "spread props are not supported");
    given.set(a.name.getText(), a);
  }
  for (const k of given.keys()) {
    if (k !== "key" && !info.data.some((f) => f.name === k) && !info.callbacks.some((c) => c.name === k)) fail(given.get(k), `<${info.name}> has no prop ${k}`);
  }
  const dataParts = info.data.map((f) => {
    const a = given.get(f.name);
    if (!a) {
      if (f.type.k === "opt") return "none";
      fail(e, `missing prop ${f.name} for <${info.name}>`);
    }
    const val = attrValue(a);
    const v = val ? expr(val, env, f.type) : { code: "true", type: T.bool };
    if (!val && f.type.k !== "bool") fail(a, `prop ${f.name} needs a value`);
    return paren(v.code);
  });
  const dataLit = `(${info.ns}.Props.mk${dataParts.map((x) => " " + x).join("")})`;
  const cbParts = info.callbacks.map((cb) => {
    const a = given.get(cb.name);
    if (!a) fail(e, `missing callback prop ${cb.name} for <${info.name}>`);
    const val = attrValue(a);
    if (!val) fail(a, "callback prop needs a function");
    const hName = m.fresh("hcb");
    const h = handlerFn(val, env, "discrete", cb.params);
    const ok = m.ob(a, "callback", `${info.name}.${cb.name} handler (passed from ${env.comp!.info.name}) preserves the invariant of ${env.comp!.info.name}, assuming ${info.name}'s callback contract`);
    return `(fun ${[...h.params, hName].join(" ")} => VReact.Emit.mk ${paren(h.code)} ${ok})`;
  });
  const cbLit = `(${info.ns}.Cb.mk${cbParts.map((c) => "\n      " + c).join("")})`;
  const ob = m.ob(e, "child-precondition", `props passed to <${info.name}> satisfy its requires(…)`);
  m.deps.add(info.ns);
  return `(${info.ns}.component.node ${dataLit}\n    ${cbLit}\n    ${ob})`;
}

/** xs.map(x => <El key={…} …/>) — a keyed list with a distinct-keys obligation. */
function keyedMap(c: ts.CallExpression, env: Env): string {
  const m = env.m;
  const pa = c.expression as ts.PropertyAccessExpression;
  const xs = expr(pa.expression, env);
  if (xs.type.k !== "arr") fail(pa.expression, ".map on a non-array");
  const fn = c.arguments[0];
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) fail(c, "map needs an inline arrow function");
  if (fn.parameters.length !== 1) fail(fn, "rendering with an index parameter is not supported (index keys are an anti-pattern): key by a stable id");
  // find the returned element to read its key
  let retEl: ts.Expression | undefined;
  if (ts.isBlock(fn.body)) {
    const r = fn.body.statements[fn.body.statements.length - 1];
    if (!r || !ts.isReturnStatement(r) || !r.expression) fail(fn, "map callback must end with return <El key=…/>");
    retEl = r.expression;
    if (fn.body.statements.slice(0, -1).some((s) => !ts.isVariableStatement(s))) fail(fn, "only const declarations may precede the returned element");
  } else retEl = fn.body;
  while (retEl && ts.isParenthesizedExpression(retEl)) retEl = retEl.expression;
  if (!retEl || !(ts.isJsxElement(retEl) || ts.isJsxSelfClosingElement(retEl))) fail(fn, "map callback must return a single JSX element with a key");
  const keyAttr = attrs(retEl).find((a) => ts.isJsxAttribute(a) && a.name.getText() === "key") as ts.JsxAttribute | undefined;
  if (!keyAttr) fail(retEl, "elements rendered from a list need a key prop (React reconciliation)");
  const keyE = attrValue(keyAttr)!;
  const p = fn.parameters[0];
  // key function
  const kEnvR = bindParam(p.name, xs.type.elem, env);
  const keyBody = (envK: Env): string => {
    const kv = expr(keyE, envK);
    if (kv.type.k === "int") return `VReact.Key.int ${paren(kv.code)}`;
    if (kv.type.k === "str") return `VReact.Key.str ${paren(kv.code)}`;
    fail(keyE, "keys must be int or string");
  };
  const keyCode = ts.isBlock(fn.body)
    ? valueBlock(fn.body.statements.slice(0, -1).concat([ts.factory.createReturnStatement(keyE)]) as unknown as ts.Statement[], kEnvR.env, undefined, fn).code
    : keyBody(kEnvR.env);
  // node function (with membership hypothesis)
  const nEnvR = bindParam(p.name, xs.type.elem, env);
  const hm = m.fresh("hmem");
  let nodeCode: string;
  if (ts.isBlock(fn.body)) {
    const bc: BlockCtx = { kind: "render", fnNode: fn, onReturn: (e, e2) => jsxNode(e!, e2) };
    nodeCode = block(fn.body.statements, 0, nEnvR.env, bc, () => fail(fn, "missing return"));
  } else nodeCode = jsxNode(fn.body, nEnvR.env);
  const ob = m.ob(keyAttr, "unique-keys", `keys ${nodeText(keyE)} are distinct across ${nodeText(pa.expression)}`);
  return `(VReact.VNode.keyedMap ${paren(xs.code)} (fun ${kEnvR.binder} => ${keyCode})\n  (fun ${nEnvR.binder} ${hm} => ${nodeCode})\n  ${ob})`;
}
