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
import { expr, prop, propAll, block, branch, handlerFn, checkDeps, hookName, specFn, symbolOf, bindParam, type BlockCtx, typeOf, valueBlock, lambda, outcome, checkClosures, topLevelHookDecls } from "./translate.ts";
import { fail, leanField, leanIdent, leanStr, jsStr, paren, nodeText, indent } from "./util.ts";

/* ─────────────────────── React 18.3.1 event model ───────────────────────
 * Native DOM events → React handler props, and their priorities, as in
 * react-dom 18.3.1 (SimpleEventPlugin, EnterLeaveEventPlugin, ChangeEventPlugin,
 * BeforeInputEventPlugin; `getEventPriority`).  All names are lower-case.        */

/** `getEventPriority`: native events with DiscreteEventPriority (flushed synchronously). */
const DISCRETE_NATIVE = new Set(["cancel", "click", "close", "contextmenu", "copy", "cut", "auxclick", "dblclick", "dragend", "dragstart", "drop", "focusin", "focusout", "input", "invalid", "keydown", "keypress", "keyup", "mousedown", "mouseup", "paste", "pause", "play", "pointercancel", "pointerdown", "pointerup", "ratechange", "reset", "resize", "seeked", "submit", "touchcancel", "touchend", "touchstart", "volumechange", "change", "selectionchange", "textinput", "compositionstart", "compositionend", "compositionupdate", "beforeblur", "afterblur", "beforeinput", "blur", "fullscreenchange", "focus", "hashchange", "popstate", "select", "selectstart"]);
/**
 * Discrete in React, but also dispatched by the DOM as a side effect, synchronously
 * inside the batch of another event or of React's commit, where the handlers before
 * them have not been rendered yet: focus moves (`autoFocus` focuses during commit,
 * after a trusted click too; a click on a `<label>` focuses its control; `el.focus()`)
 * fire `focusout` on the element losing focus — anywhere in the app — and `focusin`;
 * form validation (a submit, `checkValidity()`) fires `invalid` at every invalid
 * control in one go.  No layout check can exclude these, so VTS checks their
 * handlers (`onFocus`, `onBlur`, `onInvalid`, and the composition fallbacks) as
 * robust, like continuous ones: they compose with whatever shares their batch.
 */
const SIDE_EFFECT_NATIVE = new Set(["focusin", "focusout", "invalid"]);
/** Handlers of this native event are checked from the render snapshot (discrete, never a side effect inside another batch). */
function snapshotNative(n: string): boolean {
  return DISCRETE_NATIVE.has(n) && !SIDE_EFFECT_NATIVE.has(n);
}
/** SimpleEventPlugin: `on${Name}` is dispatched by the native event `name` (lower-cased). */
const SIMPLE_EVENTS = ["abort", "auxClick", "cancel", "canPlay", "canPlayThrough", "click", "close", "contextMenu", "copy", "cut", "drag", "dragEnd", "dragEnter", "dragExit", "dragLeave", "dragOver", "dragStart", "drop", "durationChange", "emptied", "encrypted", "ended", "error", "gotPointerCapture", "input", "invalid", "keyDown", "keyPress", "keyUp", "load", "loadedData", "loadedMetadata", "loadStart", "lostPointerCapture", "mouseDown", "mouseMove", "mouseOut", "mouseOver", "mouseUp", "paste", "pause", "play", "playing", "pointerCancel", "pointerDown", "pointerMove", "pointerOut", "pointerOver", "pointerUp", "progress", "rateChange", "reset", "resize", "seeked", "seeking", "stalled", "submit", "suspend", "timeUpdate", "touchCancel", "touchEnd", "touchStart", "volumeChange", "scroll", "toggle", "touchMove", "waiting", "wheel"];
/** React prop (without `on`) → the native events that can dispatch it (onChange: see `changeNatives`). */
const REACT_EVENTS: Record<string, string[]> = {
  ...Object.fromEntries(SIMPLE_EVENTS.map((n) => [n[0].toUpperCase() + n.slice(1), [n.toLowerCase()]])),
  AnimationEnd: ["animationend"], AnimationIteration: ["animationiteration"], AnimationStart: ["animationstart"],
  TransitionEnd: ["transitionend"], DoubleClick: ["dblclick"], Focus: ["focusin"], Blur: ["focusout"],
  // EnterLeaveEventPlugin: one native mouseout/mouseover dispatches leave *and* enter
  MouseEnter: ["mouseout", "mouseover"], MouseLeave: ["mouseout", "mouseover"],
  PointerEnter: ["pointerout", "pointerover"], PointerLeave: ["pointerout", "pointerover"],
  // BeforeInputEventPlugin (native textInput, or the keypress/paste/composition fallback)
  BeforeInput: ["textinput", "keypress", "paste", "compositionend"],
  // composition events (native, or the keydown/keyup/keypress/mousedown/focusout fallback)
  CompositionStart: ["compositionstart", "focusout", "keydown", "keypress", "keyup", "mousedown"],
  CompositionEnd: ["compositionend", "focusout", "keydown", "keypress", "keyup", "mousedown"],
  CompositionUpdate: ["compositionupdate", "focusout", "keydown", "keypress", "keyup", "mousedown"],
};
/** ChangeEventPlugin `isTextInputElement`: input types whose onChange comes from `input`/`change`. */
const TEXT_INPUT_TYPES = new Set(["color", "date", "datetime", "datetime-local", "email", "month", "number", "password", "range", "search", "tel", "text", "time", "url", "week"]);
const EVENT_RENAME: Record<string, string> = { doubleclick: "dblclick" };

/** The attributes of `e` named `name` up to letter case (React sets unknown props as attributes, which HTML lower-cases). */
function attrsNamed(e: ts.JsxElement | ts.JsxSelfClosingElement, name: string): ts.JsxAttribute[] {
  return attrs(e).filter((x): x is ts.JsxAttribute => ts.isJsxAttribute(x) && x.name.getText().toLowerCase() === name);
}

/** A static string value of attribute `name` on element `e` (`"x"` or `{"x"}`); null if absent, undefined if not static (or given twice). */
function staticAttr(e: ts.JsxElement | ts.JsxSelfClosingElement, name: string): string | null | undefined {
  const as = attrsNamed(e, name);
  if (as.length === 0) return null;
  if (as.length > 1) return undefined;
  const a = as[0];
  const v = a.initializer && ts.isJsxExpression(a.initializer) ? a.initializer.expression : a.initializer;
  return v && ts.isStringLiteralLike(v) ? v.text : undefined;
}

/** ChangeEventPlugin: the native events that dispatch `onChange` on `<tag>` (also bubbled from descendants). */
function changeNatives(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement): string[] {
  const any = ["click", "input", "change"];
  if (tag === "select") return ["change"];
  if (tag === "textarea") return ["input", "change"];
  if (tag !== "input") return any; // a change of any form control inside bubbles here
  const t = staticAttr(e, "type");
  if (t === undefined) return any; // dynamic type: checkbox/radio (click) or text-like (input)
  const ty = (t ?? "text").toLowerCase();
  if (ty === "checkbox" || ty === "radio") return ["click"]; // shouldUseClickEvent
  if (ty === "file") return ["change"];
  // isTextInputElement (an unknown type is "text"); hidden/button/submit/reset/image: conservatively any
  return TEXT_INPUT_TYPES.has(ty) || !["hidden", "button", "submit", "reset", "image"].includes(ty) ? ["input", "change"] : any;
}

interface EventInfo {
  /** handler name in the model (`Handler.event`) */
  model: string;
  /** native events that can run this handler */
  natives: string[];
  /** discrete iff every native event has DiscreteEventPriority and is never a side effect (`snapshotNative`) */
  discrete: boolean;
  /** why a non-discrete handler is checked robust (for the obligation text) */
  why: string;
}

/** Classify the handler prop `name` (`onX`) on the intrinsic element `<tag>`; rejects what React would not dispatch faithfully. */
function eventInfo(name: string, tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, at: ts.Node): EventInfo {
  const x = name.slice(2);
  if (x === "Select") fail(at, `onSelect is not supported in VTS: React dispatches it to the focused element from mouseup/keydown/keyup/selectionchange, alongside other handlers`);
  const natives = x === "Change" ? changeNatives(tag, e) : REACT_EVENTS[x];
  if (!natives) {
    const base = x.endsWith("Capture") ? x.slice(0, -7) : "";
    if (base && (REACT_EVENTS[base] || base === "Change" || base === "Select")) fail(at, `capture-phase handlers (${name}) are not supported in VTS: use on${base}`);
    fail(at, `unknown event handler ${name}: React 18 does not dispatch it (check the spelling)`);
  }
  let model = x.toLowerCase();
  model = EVENT_RENAME[model] ?? model;
  const side = "the DOM also dispatches it inside the batch of another event or of a commit, before their updates are rendered";
  const why = !natives.every((n) => DISCRETE_NATIVE.has(n))
    ? "continuous/default-priority event: rendered later, may see a stale snapshot"
    : natives.length === 1
      ? `focus/blur/invalid event: ${side}`
      : `also dispatched by focusout (React's composition fallback): ${side}`;
  return { model, natives, discrete: natives.every(snapshotNative), why };
}

/** Whether `onX` (on an intrinsic element) is a discrete handler; unknown or rejected names count as not discrete. */
function isDiscreteProp(name: string): boolean {
  const x = name.slice(2);
  if (x === "Change") return true; // click / input / change: all discrete
  const natives = REACT_EVENTS[x];
  return !!natives && natives.every(snapshotNative);
}

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
  // the Lean namespace of the component: renamed when the name is a Lean token or Lean name (`Type`, `List`, …)
  return { name, ns: `${ns}.${leanIdent(name)}`, module, data, callbacks, decl: fn, trusted, propsType };
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
  // closures (handlers, effects, updaters, callbacks) over render-local `let`s must agree with JS
  if (!info.trusted) checkClosures(body, env);
  const pp = prepass(body.statements, env, comp, m);
  comp.stateVars = pp.stateVars;
  deferredFields.set(comp, computeDeferred(body, comp, env));

  // ---- declarations ----
  let out = `namespace ${leanIdent(info.name)}\n\n`;
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
      jsxConst: jsxConstCtx(comp),
    };
    (bc as BlockCtx & { onEffect?: (c: ts.CallExpression, env: Env) => void }).onEffect = (c, env2) => {
      effects.push(effectCode(c, env2, info));
    };
    const renderBody = withBubble(NO_BUBBLE, () => renderBlock(pp.renderStmts, renv, bc));
    out += `${sig} :=\n  ${lets}${renderBody}\n\n`;
  }
  out += `def component : VReact.Component spec := ⟨fun d cb s hpre hinv => render d cb s hpre hinv⟩\n\n`;
  out += `end ${leanIdent(info.name)}\n`;
  return out;
}

/* ───────────── deferred updates (React 18 lanes; SEMANTICS §2.2) ─────────────
 * Updates queued by effects (setup or timers) and by continuous/default-priority
 * handlers are rendered later than discrete ones.  React keeps one queue per hook
 * and rebases: a discrete update is rendered first, skipping a pending deferred
 * one, and is later re-applied on top of it.  So in a component with deferred
 * sources, the discrete handlers and the callbacks it implements for children are
 * checked `RebaseSafe`: from every invariant state that agrees with the snapshot
 * on the fields no deferred source writes.  Without deferred sources this is the
 * plain snapshot check.                                                        */

const deferredFields = new WeakMap<CompCtx, StateVar[]>();

/** State fields of `comp` that a deferred source may write (in state order). */
function deferredOf(comp: CompCtx): StateVar[] {
  return deferredFields.get(comp) ?? [];
}

/** Syntactic over-approximation: setters/dispatches reachable (through local closures) from an effect or a non-discrete handler. */
function computeDeferred(body: ts.Block, comp: CompCtx, env: Env): StateVar[] {
  const checker = env.m.checker;
  const setters = new Map<ts.Symbol, StateVar>();
  const closures = new Map<ts.Symbol, ts.Node>();
  const collect = (n: ts.Node) => {
    if (ts.isVariableDeclaration(n) && n.initializer) {
      if (ts.isIdentifier(n.name)) {
        const sym = checker.getSymbolAtLocation(n.name);
        if (sym) closures.set(sym, n.initializer);
      } else if (ts.isArrayBindingPattern(n.name) && ts.isCallExpression(n.initializer) && ["useState", "useReducer"].includes(hookName(env, n.initializer.expression) ?? "")) {
        const [a, b] = n.name.elements;
        if (a && b && ts.isBindingElement(a) && ts.isIdentifier(a.name) && ts.isBindingElement(b) && ts.isIdentifier(b.name)) {
          const sv = comp.stateVars.find((x) => x.name === (a.name as ts.Identifier).text);
          const sym = checker.getSymbolAtLocation(b.name);
          if (sv && sym) setters.set(sym, sv);
        }
      }
    }
    if (ts.isFunctionDeclaration(n) && n.name) {
      const sym = checker.getSymbolAtLocation(n.name);
      if (sym) closures.set(sym, n);
    }
    ts.forEachChild(n, collect);
  };
  collect(body);
  const acc = new Set<StateVar>();
  const seen = new Set<ts.Node>();
  const writes = (n: ts.Node) => {
    if (ts.isIdentifier(n)) {
      const sym = checker.getSymbolAtLocation(n);
      const sv = sym && setters.get(sym);
      if (sv) acc.add(sv);
      const c = sym && closures.get(sym);
      if (c && !seen.has(c)) {
        seen.add(c);
        writes(c);
      }
    }
    ts.forEachChild(n, writes);
  };
  const visit = (n: ts.Node) => {
    if (ts.isCallExpression(n) && ["useEffect", "useLayoutEffect"].includes(hookName(env, n.expression) ?? "")) n.arguments.forEach(writes);
    if (ts.isJsxAttribute(n) && n.initializer && /^on[A-Z]/.test(n.name.getText()) && /^[a-z]/.test(n.parent.parent.tagName.getText()) && !isDiscreteProp(n.name.getText())) writes(n.initializer);
    ts.forEachChild(n, visit);
  };
  visit(body);
  return comp.stateVars.filter((s) => acc.has(s));
}

/** `vary` (the snapshot with the deferred fields replaced by `x`) and `x₀` (their snapshot values), for `RebaseSafe`. */
function rebase(comp: CompCtx): { vary: string; x0: string; names: string } {
  const d = deferredOf(comp);
  const snap = comp.snap;
  const ts1 = d.map((s) => leanType(s.type));
  const X = ts1.length === 1 ? ts1[0] : `(${ts1.join(" × ")})`;
  const proj = (i: number) => (d.length === 1 ? "x" : i < d.length - 1 ? `x${".2".repeat(i)}.1` : `x${".2".repeat(i)}`);
  const vary = `(fun (x : ${X}) => { ${snap} with ${d.map((s, i) => `${leanField(s.field)} := ${proj(i)}`).join(", ")} })`;
  const fields = d.map((s) => `${snap}.${leanField(s.field)}`);
  const x0 = d.length === 1 ? fields[0] : `(${fields.join(", ")})`;
  return { vary, x0, names: d.map((s) => s.name).join(", ") };
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
  // several requires / invariants form one condition each, in order: a later one may use
  // the earlier ones as guards (`propAll`, as for function preconditions)
  const reqs: ts.Expression[] = [];
  const invs: ts.Expression[] = [];
  for (const s of stmts) {
    if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression)) {
      const c = s.expression;
      const sf = specFn(env, c.expression);
      if (sf === "requires" || sf === "invariant") {
        if (c.arguments.length !== 1) fail(c, `${sf}(condition)`);
        (sf === "requires" ? reqs : invs).push(c.arguments[0]);
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
        const prop = `${paren(l.body.code)} = true`;
        const prev = pp.contracts.get(cb.name);
        if (!prev) pp.contracts.set(cb.name, { binders: l.binders, prop });
        else {
          // several contracts for one callback: all of them hold (conjunction), the
          // later one's parameters renamed to the first one's binders (simultaneously)
          const binders = [...prev.binders];
          for (let i = binders.length; i < l.binders.length; i++) {
            let nb = l.binders[i];
            for (let k = 1; binders.includes(nb); k++) nb = `${l.binders[i]}_${k}`;
            binders.push(nb);
          }
          const same = l.binders.every((b, i) => b === binders[i]);
          const later = same ? paren(prop) : `((fun ${l.typed.join(" ")} => ${prop})${l.binders.map((_, i) => " " + binders[i]).join("")})`;
          pp.contracts.set(cb.name, { binders, prop: `${prev.prop} ∧ ${later}` });
        }
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
      // useMemo / useCallback: allowed only here (top level), before any early return
      for (const dd of s.declarationList.declarations) {
        const init = dd.initializer && ts.isParenthesizedExpression(dd.initializer) ? dd.initializer.expression : dd.initializer;
        if (!init || !ts.isCallExpression(init)) continue;
        const h = hookName(env, init.expression);
        if (h !== "useMemo" && h !== "useCallback") continue;
        if (sawNonHook) fail(dd, "hooks must run unconditionally before any early return (Rules of Hooks)");
        topLevelHookDecls.add(dd);
      }
    }
    if (ts.isIfStatement(s) || ts.isReturnStatement(s) || ts.isSwitchStatement(s) || mayReturn(s)) sawNonHook = true;
    pp.renderStmts.push(s);
  }
  // (an invariant can only mention state declared before it: TypeScript rejects the rest)
  if (reqs.length) pp.pre.push(propAll(reqs, env));
  if (invs.length) pp.inv.push(propAll(invs, stateEnv));
  return pp;
}

/** Does a statement of the component body contain a `return` of the component (not of a nested function)? */
function mayReturn(s: ts.Node): boolean {
  if (ts.isReturnStatement(s)) return true;
  if (ts.isFunctionLike(s) || ts.isClassLike(s)) return false;
  return !!ts.forEachChild(s, (c) => (mayReturn(c) ? true : undefined));
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
  let stmts = ts.isBlock(fn.body) ? [...fn.body.statements] : [ts.factory.createExpressionStatement(fn.body)];
  let bodyE: ts.Node = fn.body;
  while (ts.isParenthesizedExpression(bodyE)) bodyE = bodyE.expression;
  if (ts.isArrowFunction(bodyE) || ts.isFunctionExpression(bodyE)) {
    // useEffect(() => () => cleanup)
    checkCleanup(bodyE, env);
    stmts = [];
  }
  const tasks: string[] = [];
  const sync: ts.Statement[] = [];
  const timerCb = (e: ts.Expression): ts.Expression | null => {
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && ["setInterval", "setTimeout"].includes(e.expression.text)) return e.arguments[0];
    return null;
  };
  for (const s of stmts) {
    if (ts.isReturnStatement(s)) {
      // cleanup: not translated, so it may not touch any component's state
      if (s.expression) checkCleanup(s.expression, env);
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
    : `(/-⟦gen⟧-/ by simp)`;
  return `(VReact.Effect.mk (S := ${info.ns}.State) (E := E) (inv := ${info.ns}.inv props) (${deps}) ${paren(setup)} ${okSetup}\n     (/-⟦gen⟧-/ by vreact_noemit)\n     [${tasks.join(", ")}] ${okTasks})`;
}

const CLEANUP_RULE = "effect cleanups may only clear timers (clearTimeout/clearInterval) and make external writes (console.*, localStorage.*, document.title = …), possibly under if/else: React runs a cleanup later, with the props and state of the render that created it, and the cleanup is not verified";

/**
 * An effect cleanup is not translated (the model has no cleanup step), so it must not be
 * able to affect any component state: only timer clearing and the documented external
 * writes, whose arguments are pure expressions, possibly under `if`/`else` with a pure
 * condition.  Setters, dispatch, parent callbacks and local helpers (which may reach
 * them) are rejected, directly or nested.
 */
function checkCleanup(e0: ts.Expression, env: Env) {
  let e: ts.Expression = e0;
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  if (!ts.isArrowFunction(e) && !ts.isFunctionExpression(e)) fail(e0, `an effect cleanup must be an inline function \`() => { … }\`; ${CLEANUP_RULE}`);
  if (e.parameters.length) fail(e, "effect cleanups take no parameters");
  checkCleanupItems(ts.isBlock(e.body) ? [...e.body.statements] : [e.body], env);
}

function checkCleanupItems(items: readonly ts.Node[], env: Env) {
  for (const it of items) {
    if (ts.isEmptyStatement(it)) continue;
    if (ts.isBlock(it)) {
      checkCleanupItems(it.statements, env);
      continue;
    }
    if (ts.isIfStatement(it)) {
      pureCleanupExpr(it.expression, env);
      checkCleanupItems([it.thenStatement], env);
      if (it.elseStatement) checkCleanupItems([it.elseStatement], env);
      continue;
    }
    let x: ts.Node = ts.isExpressionStatement(it) ? it.expression : it;
    while (ts.isParenthesizedExpression(x)) x = x.expression;
    if (ts.isCallExpression(x)) {
      const callee = x.expression;
      const timerClear = ts.isIdentifier(callee) && ["clearTimeout", "clearInterval"].includes(callee.text) && !env.vars.get(symbolOf(env, callee)!);
      const external = ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) && ["console", "localStorage"].includes(callee.expression.text) && !env.vars.get(symbolOf(env, callee.expression)!);
      if (timerClear || external) {
        x.arguments.forEach((a) => pureCleanupExpr(a, env));
        continue;
      }
    }
    if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.EqualsToken && x.left.getText() === "document.title") {
      pureCleanupExpr(x.right, env);
      continue;
    }
    if (ts.isCallExpression(x) && updatesState(x.expression, env)) fail(it, `effect cleanups may not update state or call parent callbacks; ${CLEANUP_RULE}`);
    fail(it, CLEANUP_RULE);
  }
}

/** Does calling `callee` reach a setter, dispatch, a parent callback or a local helper? */
function updatesState(callee: ts.Expression, env: Env): boolean {
  if (ts.isIdentifier(callee)) {
    const b = env.vars.get(symbolOf(env, callee)!);
    return !!b && b.k !== "val";
  }
  if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) && env.vars.get(symbolOf(env, callee.expression)!)?.k === "props") {
    return !env.comp?.info.data.some((f) => f.name === callee.name.text);
  }
  return false;
}

/** Arguments inside a cleanup: data only (no state updates, callbacks, helpers or unknown calls). */
function pureCleanupExpr(n: ts.Node, env: Env) {
  const visit = (x: ts.Node) => {
    if (ts.isCallExpression(x)) {
      const callee = x.expression;
      let ok = false;
      if (ts.isIdentifier(callee)) {
        const s = symbolOf(env, callee);
        const d = s && (s.flags & ts.SymbolFlags.Alias ? env.m.checker.getAliasedSymbol(s) : s).declarations?.[0];
        ok = !env.vars.get(s!) && (callee.text === "String" || !!specFn(env, callee) || (!!d && env.m.prog.globals.get(d)?.k === "fn"));
      } else if (ts.isPropertyAccessExpression(callee)) {
        // methods of data values (arrays, strings) and Math.*; not props callbacks or helpers
        const root = callee.expression;
        if (ts.isIdentifier(root)) {
          const b = env.vars.get(symbolOf(env, root)!);
          ok = root.text === "Math" || b?.k === "val" || (!b && !!globalConst(root, env));
        } else ok = !(ts.isPropertyAccessExpression(root) && updatesState(root, env));
      }
      if (!ok) fail(x, `effect cleanups may not call \`${nodeText(callee, 40)}\` here; ${CLEANUP_RULE}`);
    }
    if (ts.isNewExpression(x) || ts.isAwaitExpression(x) || ts.isDeleteExpression(x)) fail(x, CLEANUP_RULE);
    if (ts.isBinaryExpression(x) && x.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && x.operatorToken.kind <= ts.SyntaxKind.LastAssignment) fail(x, CLEANUP_RULE);
    if ((ts.isPrefixUnaryExpression(x) || ts.isPostfixUnaryExpression(x)) && (x.operator === ts.SyntaxKind.PlusPlusToken || x.operator === ts.SyntaxKind.MinusMinusToken)) fail(x, CLEANUP_RULE);
    ts.forEachChild(x, visit);
  };
  visit(n);
}

function globalConst(id: ts.Identifier, env: Env) {
  let s = symbolOf(env, id);
  if (s && s.flags & ts.SymbolFlags.Alias) s = env.m.checker.getAliasedSymbol(s);
  const d = s?.declarations?.[0];
  const g = d ? env.m.prog.globals.get(d) : undefined;
  return g?.k === "const" ? g : undefined;
}

/* ───────────────────────────── JSX ───────────────────────────── */

function isJsx(e: ts.Node): boolean {
  return ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e) || ts.isJsxFragment(e);
}

/** How render blocks translate a JSX const at its declaration: a VNode of this render. */
function jsxConstCtx(comp: CompCtx): NonNullable<BlockCtx["jsxConst"]> {
  return { code: (e, env) => jsxNode(e, env), type: `VReact.VNode ${comp.stateType} E (${comp.invName} ${comp.propsVar}) ${comp.snap}` };
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
    if (b?.k === "jsx") {
      // translated (its obligations checked) at the declaration; translated again here
      // only for the event-bubbling checks of this position
      env.m.dryRun(() => jsxNode(b.node, { ...b.env, scope: env.scope }));
      return b.code;
    }
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
      // React renders nothing for booleans, but JS evaluates the expression: keep it (and its obligations)
      return `(VReact.VNode.ofBool ${paren(v.code)})`;
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
 * Event bubbling, multi-handler events and activation chains.  One native DOM
 * event runs, in one batch and from one render snapshot, the handlers of its
 * target and of all its ancestors — and every React prop it maps to: a checkbox
 * click runs `onClick` and `onChange`, an `input` event runs `onInput` and
 * `onChange` (react-dom ChangeEventPlugin).  A click also runs its target's
 * *activation behaviour* before React renders when the click was dispatched by a
 * script (`el.click()`, `dispatchEvent`, testing libraries, jsdom): React flushes
 * discrete updates in a microtask, and none runs inside that call.
 *
 *  - A submit button (`<button>` not of type button/reset, `<input type=submit|image>`)
 *    fires `submit` at its form owner, a reset button `reset`; both bubble.
 *  - A `<label>` (a click on it, or on non-interactive content inside it) focuses
 *    its control and dispatches a second `click` to it — through the label and its
 *    ancestors again when the control is inside it.
 *  - A checkbox / radio fires `input` and `change`, but React renders first: its
 *    ChangeEventPlugin flushes to restore the controlled value (`finishEventHandler`).
 *  - An invoker button (`commandfor` / `command`) runs a command on an element
 *    anywhere; `request-close` fires `cancel` at a dialog (Chromium).
 *  - `<details>` toggles and popovers toggle (`toggle` is a queued task; React 18
 *    has no `onBeforeToggle`); links navigate; a dialog's `close` is a queued task.
 *
 * Implicit submission by Enter and the keyboard activation of buttons follow
 * trusted key events only, which the browser dispatches from native code, with
 * microtask checkpoints in between.  The model runs one handler per event, so VTS
 * rejects every layout in which one discrete event, with its activation behaviour,
 * could run two discrete handlers, or one twice: two handler props of one element
 * sharing a native event; an element with handlers containing a descendant handler
 * that shares a native event, or a user component; `onClick` on, around, or (not
 * inside interactive content) within a submit/reset button whose form owner has
 * `onSubmit`/`onReset` at or above it — or that names its form (`form=…`), which may
 * be anywhere —, an invoker button, or a `<label>`; a user component within such a
 * button or a label.
 * Focus and `invalid` events are side effects (`SIDE_EFFECT_NATIVE`): robust.
 *
 * `bubble` describes the enclosing elements during the (synchronous, recursive)
 * translation of a component's JSX, so it also covers JSX reached through local
 * consts, conditionals and `.map`.  No element of another component encloses a
 * handler here (a component inside an element with handlers is rejected), so the
 * form owner and every handler a bubbling event reaches lie in this component.
 */
interface Bubble {
  /** native event → the enclosing handler it reaches (`onClick on <li>`) */
  natives: Map<string, string>;
  handlers: string[];
  /** the enclosing `onClick` handler (`onClick on <li>`) */
  onClick: string | null;
  /** inside a `<form>` of this component: the handlers its `submit` / `reset` event reaches (on the form or above it) */
  form: { submit: string | null; reset: string | null } | null;
  /** the nearest enclosing element whose activation by a click inside it dispatches another event that reaches a handler */
  act: Activation | null;
}
interface Activation {
  /** `a <label>`, `a submit button <button> of a form with onSubmit on <form>` */
  what: string;
  label: boolean;
}
const NO_BUBBLE: Bubble = { natives: new Map(), handlers: [], onClick: null, form: null, act: null };
let bubble: Bubble = NO_BUBBLE;

function withBubble<T>(b: Bubble, f: () => T): T {
  const saved = bubble;
  bubble = b;
  try {
    return f();
  } finally {
    bubble = saved;
  }
}

/** Input types with an activation behaviour of their own: a click on them activates them, not an enclosing button. */
const ACTIVATING_INPUTS = new Set(["checkbox", "radio", "submit", "image", "reset", "button", "file", "color"]);

/** `<button>` / `<input>`: may a click on it submit / reset its form owner?  A dynamic `type` may do either. */
function formActivation(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement): { submit: boolean; reset: boolean } {
  const t = staticAttr(e, "type");
  if (tag !== "button" && tag !== "input") return { submit: false, reset: false };
  if (t === undefined) return { submit: true, reset: true };
  if (tag === "button") {
    const ty = (t ?? "").toLowerCase(); // missing or invalid: the submit button state
    return { submit: ty !== "button" && ty !== "reset", reset: ty === "reset" };
  }
  const ty = (t ?? "text").toLowerCase();
  return { submit: ty === "submit" || ty === "image", reset: ty === "reset" };
}

/**
 * Does a click on (or inside) `<tag>` stop there, instead of activating an
 * enclosing submit/reset button (`label` false) or label (`label` true)?  An
 * element with an activation behaviour of its own is the click's activation
 * target; a label also ignores clicks on interactive content inside it.  Unsure
 * cases (a dynamic `type` or `href`) do not stop it.
 */
function stopsActivation(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, label: boolean): boolean {
  if (tag === "button" || tag === "label" || tag === "summary") return true;
  if (tag === "a" || tag === "area") return typeof staticAttr(e, "href") === "string";
  if (tag === "input") {
    const t = staticAttr(e, "type");
    if (t === undefined) return false;
    const ty = (t ?? "text").toLowerCase();
    return label ? ty !== "hidden" : ACTIVATING_INPUTS.has(ty);
  }
  return label && ["select", "textarea", "details"].includes(tag);
}

/** Check the handler props of `<tag>` against each other and the enclosing elements; returns the context for its children. */
function checkEvents(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, handlers: ts.JsxAttribute[], infos: Map<ts.JsxAttribute, EventInfo>): Bubble {
  const own = new Map<string, string>();
  for (const a of handlers) {
    const name = a.name.getText();
    for (const n of infos.get(a)!.natives) {
      // Robust handlers (continuous/default-priority, focus, invalid) cannot call
      // parents: several of them in one batch compose.  Discrete ones cannot.
      if (!snapshotNative(n)) continue;
      const other = own.get(n);
      if (other && other !== name) fail(a, `${other} and ${name} on <${tag}> both run on one native "${n}" event: React calls both in one batch, from the same snapshot (keep one handler)`);
      const anc = bubble.natives.get(n);
      if (anc) fail(a, `${name} on <${tag}> is nested inside an element with ${anc}: one native "${n}" event would run both (event bubbling)`);
      own.set(n, name);
    }
  }
  const names = handlers.map((a) => a.name.getText());
  const onClick = names.includes("onClick");
  const SCRIPTED = "in one batch when a script dispatches the click (el.click(), testing libraries)";
  // activation: an enclosing activator still activated by a click here, and this element's own
  const enclosing = bubble.act && !stopsActivation(tag, e, bubble.act.label) ? bubble.act : null;
  let mine: Activation | null = null;
  const fa = formActivation(tag, e);
  if (tag === "label") {
    mine = { what: "a <label>", label: true };
    const why = "a click on a label (or on non-interactive content inside it) is dispatched again to its control (the element htmlFor names, or the first form control inside it)";
    if (onClick) fail(e, `onClick on <label>: ${why}, so one click would run this handler twice, or with the control's handlers, ${SCRIPTED} (put the handler on the control, or on an element outside the label)`);
    if (bubble.onClick) fail(e, `<label> nested inside an element with ${bubble.onClick}: ${why}, so one click would run that handler twice, ${SCRIPTED} (move the handler)`);
  } else if (fa.submit || fa.reset) {
    // the handler its form's submit / reset event reaches; with form=… the form may be anywhere
    const named = attrsNamed(e, "form").length > 0;
    const reach = (k: "submit" | "reset") => (!fa[k] ? null : named ? `may run on${k === "submit" ? "Submit" : "Reset"} anywhere: form=… names its form` : bubble.form?.[k] ? `runs ${bubble.form[k]}` : null);
    const k = reach("submit") ? "submit" : reach("reset") ? "reset" : null;
    if (k) {
      const on = k === "submit" ? "onSubmit" : "onReset";
      mine = { what: `a ${k} button <${tag}> (${k === "submit" ? "submitting" : "resetting"} its form ${reach(k)})`, label: false };
      const fix = `use type="button", or put the logic in ${on}`;
      if (onClick) fail(e, `onClick on ${mine.what}: one click runs both handlers, ${SCRIPTED} (${fix})`);
      if (bubble.onClick) fail(e, `${mine.what} is nested inside an element with ${bubble.onClick}: one click runs both handlers, ${SCRIPTED} (move the handler, or ${fix})`);
    }
  }
  // an invoker button (commandfor / command) runs a command on an element anywhere:
  // `request-close` fires `cancel` at a dialog synchronously (its onCancel, in Chromium)
  if (!mine && tag === "button" && (attrsNamed(e, "commandfor").length || attrsNamed(e, "command").length)) {
    mine = { what: "a command button <button> (commandfor/command: the element it controls, anywhere, may run a handler — request-close fires cancel at a dialog)", label: false };
    if (onClick) fail(e, `onClick on ${mine.what}: one click runs both handlers, ${SCRIPTED} (put the logic in the target's handler)`);
    if (bubble.onClick) fail(e, `${mine.what} is nested inside an element with ${bubble.onClick}: one click runs both handlers, ${SCRIPTED} (move the handler)`);
  }
  if (enclosing && onClick) fail(e, `onClick on <${tag}> inside ${enclosing.what}: one click runs this handler and, through the activation of the enclosing element, another one (or this one again), ${SCRIPTED} (move the handler out)`);
  const natives = new Map(bubble.natives);
  for (const [n, p] of own) natives.set(n, `${p} on <${tag}>`);
  const handlerOf = (prop: string) => (names.includes(prop) ? `${prop} on <${tag}>` : null);
  return {
    natives,
    handlers: [...bubble.handlers, ...names],
    onClick: onClick ? `onClick on <${tag}>` : bubble.onClick,
    form: tag === "form" ? { submit: handlerOf("onSubmit") ?? bubble.natives.get("submit") ?? null, reset: handlerOf("onReset") ?? bubble.natives.get("reset") ?? null } : bubble.form,
    act: mine ?? enclosing,
  };
}

function intrinsic(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  const comp = env.comp!;
  const handlerAttrs = attrs(e).filter(ts.isJsxAttribute).filter((a) => /^on[A-Z]/.test(a.name.getText()));
  const infos = new Map(handlerAttrs.map((a) => [a, eventInfo(a.name.getText(), tag, e, a)] as const));
  const inner = checkEvents(tag, e, handlerAttrs, infos);
  const as: string[] = [];
  const hs: string[] = [];
  let key: string | null = null;
  for (const a of attrs(e)) {
    if (ts.isJsxSpreadAttribute(a)) fail(a, "spread attributes are not supported");
    const name = a.name.getText();
    if (name === "key") {
      key = keyExpr(a, e, env);
      continue;
    }
    if (name === "ref" || name === "dangerouslySetInnerHTML") fail(a, `${name} is not supported in VTS`);
    const val = attrValue(a);
    if (/^on[A-Z]/.test(name)) {
      if (!val) fail(a, "handler attribute needs a value");
      const info = infos.get(a)!;
      const ev = info.model;
      const h = handlerFn(val, env, info.discrete ? "discrete" : "robust", "event");
      const run = `(fun ${h.params[0] ?? "_"} => ${h.code})`;
      if (!info.discrete) {
        const ok = m.ob(a, "handler-robust", `${name} handler on <${tag}> (${info.why}) preserves the invariant of ${comp.info.name} from any state`);
        hs.push(`(VReact.Handler.continuous ${leanStr(ev)} ${run} ${ok}\n    (/-⟦gen⟧-/ by vreact_noemit))`);
      } else if (deferredOf(comp).length) {
        const r = rebase(comp);
        const ok = m.ob(a, "handler-rebased", `${name} handler on <${tag}> preserves the invariant of ${comp.info.name} also when React rebases it onto pending updates of ${r.names} (timers/effects/continuous handlers)`);
        hs.push(`(VReact.Handler.rebased ${leanStr(ev)} ${run}\n    ${r.vary} ${r.x0} (/-⟦gen⟧-/ rfl) hinv\n    ${ok}\n    (/-⟦gen⟧-/ by decide))`);
      } else {
        const ok = m.ob(a, "handler", `${name} handler on <${tag}> preserves the invariant of ${comp.info.name}`);
        hs.push(`(VReact.Handler.discrete ${leanStr(ev)} ${run} ${ok}\n    (/-⟦gen⟧-/ by decide))`);
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
  const ch = kids ? withBubble(inner, () => children(kids, env)) : "VReact.VList.nil";
  return withKey(key, `(VReact.VNode.elem ${leanStr(tag)} [${as.join(", ")}]\n  [${hs.join(",\n   ")}]\n  ${ch})`);
}

/** Elements returned by `xs.map(…)`, whose key is translated (as the key function) by `keyedMap`. */
const keyedByMap = new WeakSet<ts.Node>();

/** The translated `key={…}` of an element outside a keyed map: JS evaluates it on every render, so its obligations count. */
function keyExpr(a: ts.JsxAttribute, e: ts.Node, env: Env): string | null {
  if (keyedByMap.has(e)) return null;
  const val = attrValue(a);
  if (!val) fail(a, "key needs a value");
  if (ts.isStringLiteral(val)) return null;
  return expr(val, env).code;
}

function withKey(key: string | null, node: string): string {
  return key === null ? node : `(VReact.VNode.withKey ${paren(key)}\n  ${node})`;
}

function componentElement(tagNode: ts.JsxTagNameExpression, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  if (bubble.handlers.length) fail(e, `<${tagNode.getText()}> is nested inside an element with ${bubble.handlers.join("/")}: its events would bubble into a second handler (move the handler, or the component, out)`);
  if (bubble.act) fail(e, `<${tagNode.getText()}> is nested inside ${bubble.act.what}: a click inside it would run its handlers and, through the activation of the enclosing element, another one, in one batch when a script dispatches the click (move the component out${bubble.act.label ? "; a label can name a control inside it with htmlFor" : ""})`);
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
    const comp = env.comp!;
    if (deferredOf(comp).length) {
      const r = rebase(comp);
      const ok = m.ob(a, "callback-rebased", `${info.name}.${cb.name} handler (passed from ${comp.info.name}) preserves the invariant of ${comp.info.name}, assuming ${info.name}'s callback contract, also when React rebases it onto pending updates of ${r.names} (timers/effects/continuous handlers)`);
      return `(fun ${[...h.params, hName].join(" ")} => VReact.Emit.rebased ${paren(h.code)}\n        ${r.vary} ${r.x0} (/-⟦gen⟧-/ rfl) hinv\n        ${ok})`;
    }
    const ok = m.ob(a, "callback", `${info.name}.${cb.name} handler (passed from ${comp.info.name}) preserves the invariant of ${comp.info.name}, assuming ${info.name}'s callback contract`);
    return `(fun ${[...h.params, hName].join(" ")} => VReact.Emit.mk ${paren(h.code)} ${ok})`;
  });
  const cbLit = `(${info.ns}.Cb.mk${cbParts.map((c) => "\n      " + c).join("")})`;
  const keyA = given.get("key");
  const key = keyA ? keyExpr(keyA, e, env) : null;
  const ob = m.ob(e, "child-precondition", `props passed to <${info.name}> satisfy its requires(…)`);
  m.deps.add(info.ns);
  return withKey(key, `(${info.ns}.component.node ${dataLit}\n    ${cbLit}\n    ${ob})`);
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
  keyedByMap.add(retEl); // its key is translated here, as the key function
  const p = fn.parameters[0];
  // key function
  const kEnvR = bindParam(p.name, xs.type.elem, env);
  const asKey = (kv: { code: string; type: VType }): string => {
    if (kv.type.k === "int") return `VReact.Key.int ${paren(kv.code)}`;
    if (kv.type.k === "str") return `VReact.Key.str ${paren(kv.code)}`;
    fail(keyE, "keys must be int or string");
  };
  const keyCode = ts.isBlock(fn.body)
    ? asKey(valueBlock(fn.body.statements.slice(0, -1).concat([ts.factory.createReturnStatement(keyE)]) as unknown as ts.Statement[], { ...kEnvR.env, keyFn: true }, undefined, fn))
    : asKey(expr(keyE, kEnvR.env));
  // node function (with membership hypothesis)
  const nEnvR = bindParam(p.name, xs.type.elem, env);
  const hm = m.fresh("hmem");
  let nodeCode: string;
  if (ts.isBlock(fn.body)) {
    const bc: BlockCtx = { kind: "render", fnNode: fn, onReturn: (e, e2) => jsxNode(e!, e2), jsxConst: jsxConstCtx(env.comp!) };
    nodeCode = block(fn.body.statements, 0, nEnvR.env, bc, () => fail(fn, "missing return"));
  } else nodeCode = jsxNode(fn.body, nEnvR.env);
  const ob = m.ob(keyAttr, "unique-keys", `keys ${nodeText(keyE)} are distinct across ${nodeText(pa.expression)}`);
  return `(VReact.VNode.keyedMap ${paren(xs.code)} (fun ${kEnvR.binder} => ${keyCode})\n  (fun ${nEnvR.binder} ${hm} => ${nodeCode})\n  ${ob})`;
}
