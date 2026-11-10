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
import { T, type VType, type Param, type Field, leanType, showType, typeOfNode, checkValueType, propertyName, isLibSymbol, collectionKind } from "./types.ts";
import { type Env, type Val, type Mark, ModCtx, type CompCtx, type CompInfo, type CallbackInfo, type StateVar, type FnInfo, type Binding, bind, freshLocal, refSymbol } from "./ctx.ts";
import { expr, prop, propAll, block, branch, handlerFn, checkDeps, hookName, specFn, isGlobal, symbolOf, globalOf, bindParam, type BlockCtx, typeOf, valueBlock, isUndefinedReturn, nsMember, contractLambda, outcome, checkClosures, topLevelHookDecls, fnParamTsTypes, stripParens, isNumeric, evalArgs, isDocumentTitle, jsxAttrText, checkPlainParams, isNullLit, ARRAY_MUTATORS, isMutatedLocal, toStr, nullishKinds } from "./translate.ts";
import { fail, leanField, leanIdent, leanStr, jsStr, paren, nodeText, indent, VtsError, jsxTextValue, asciiLower, relLoc } from "./util.ts";
import { reservedName, windowReserved } from "./domNames.ts";

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

/** The attributes of `e` named `name` up to ASCII letter case (React sets unknown props as attributes, whose names HTML ASCII-lower-cases). */
function attrsNamed(e: ts.JsxElement | ts.JsxSelfClosingElement, name: string): ts.JsxAttribute[] {
  return attrs(e).filter((x): x is ts.JsxAttribute => ts.isJsxAttribute(x) && asciiLower(x.name.getText()) === name);
}

/**
 * The values attribute `name` of `e` may have, ASCII-lower-cased (HTML matches the keywords of
 * enumerated attributes such as `type` ASCII-case-insensitively): `[]` when it is absent; one
 * value for a string; both branches of a conditional `c ? "text" : "password"`; the members of
 * an enum-typed expression.  Undefined when unknown (another expression, or the attribute given
 * twice up to case).
 */
function attrValues(e: ts.JsxElement | ts.JsxSelfClosingElement, name: string, env: Env): string[] | undefined {
  const as = attrsNamed(e, name);
  if (as.length === 0) return [];
  if (as.length > 1) return undefined;
  const a = as[0];
  if (!a.initializer) return [""];
  if (ts.isStringLiteral(a.initializer)) return [asciiLower(jsxAttrText(a.initializer))];
  if (!ts.isJsxExpression(a.initializer) || !a.initializer.expression) return undefined;
  const of = (x0: ts.Expression): string[] | undefined => {
    const x = stripParens(x0);
    if (ts.isStringLiteralLike(x)) return [asciiLower(x.text)];
    if (ts.isConditionalExpression(x)) {
      const l = of(x.whenTrue);
      const r = of(x.whenFalse);
      return l && r ? [...l, ...r] : undefined;
    }
    let t: VType;
    try {
      t = typeOf(x, env);
    } catch (err) {
      if (err instanceof VtsError) return undefined; // translated (and rejected, if so) as the attribute
      throw err;
    }
    return t.k === "enum" ? env.m.reg.enumLits(t).map(asciiLower) : undefined;
  };
  return of(a.initializer.expression);
}

/** A static string value of attribute `name` on element `e` (`"x"` or `{"x"}`); null if absent, undefined if not static (or given twice). */
function staticAttr(e: ts.JsxElement | ts.JsxSelfClosingElement, name: string): string | null | undefined {
  const as = attrsNamed(e, name);
  if (as.length === 0) return null;
  if (as.length > 1) return undefined;
  const a = as[0];
  const v = a.initializer && ts.isJsxExpression(a.initializer) ? a.initializer.expression : a.initializer;
  return v && ts.isStringLiteralLike(v) ? jsxAttrText(v) : undefined;
}

/**
 * ChangeEventPlugin: the native events that dispatch `onChange` on `<tag>` (also bubbled from
 * descendants).  `html`: whether the element is an HTML element; inside `<svg>` / `<math>` an
 * `<input>` is an SVG (MathML) element, which has no `type` and none of an input's events of
 * its own: only changes bubbling from HTML controls inside a `<foreignObject>` reach it.
 */
function changeNatives(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, html: boolean): string[] {
  const any = ["click", "input", "change"];
  if (!html) return any;
  if (tag === "select") return ["change"]; // its content is options only (CONTENT_RULES), which make no onChange
  if (tag === "textarea") return ["input", "change"];
  if (tag !== "input") return any; // a change of any form control inside bubbles here
  const t = staticAttr(e, "type");
  if (t === undefined) return any; // dynamic type: checkbox/radio (click) or text-like (input)
  const ty = asciiLower(t ?? "text");
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
function eventInfo(name: string, tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, at: ts.Node, html: boolean): EventInfo {
  const x = name.slice(2);
  if (x === "Select") fail(at, `onSelect is not supported in VTS: React dispatches it to the focused element from mouseup/keydown/keyup/selectionchange, alongside other handlers`);
  const natives = x === "Change" ? changeNatives(tag, e, html) : REACT_EVENTS[x];
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

/**
 * The JSX attribute names React 18.3.1 keeps out of an element's props besides `key` and `ref`
 * (`RESERVED_PROPS` of `React.createElement` and `react/jsx-runtime`): the development JSX
 * transforms pass the source location and `this` under these names.  A component never
 * receives them, and an HTML element never gets them as attributes.
 */
const RESERVED_PROPS = ["__self", "__source"];
const RESERVED_WHY = (name: string) => `React 18 removes ${name} from the props of every element, like key and ref (the development JSX transform passes ${name === "__source" ? "the source location" : "`this`"} under that name): a component never receives it (props.${name} is undefined), an HTML element never gets it as an attribute`;

export function baseEnv(m: ModCtx): Env {
  return { m, vars: new Map(), narrow: new Map(), scope: new Set(RESERVED), mode: "code" };
}

/** Collect the signature of a component (props split into data and callbacks). */
export function compSignature(fn: ts.FunctionDeclaration, ns: string, module: string, m: ModCtx, trusted: boolean): CompInfo {
  const name = fn.name!.text;
  checkPlainParams(fn.parameters, `the component ${name}`);
  const p = fn.parameters[0];
  if (fn.parameters.length > 1) fail(fn.parameters[1], "components take a single props parameter");
  let data: Field[] = [];
  const callbacks: { name: string; params: Param[] }[] = [];
  let propsType: VType | null = null;
  if (p) {
    if (!p.type) fail(p, "annotate the props parameter type");
    propsType = typeOfNode(p.type, m.prog.typeEnv, name + "Props");
    if (propsType.k !== "rec") fail(p, "props must be an object type");
    // React 18 takes `key`, `ref`, `__self` and `__source` out of the props: the component never
    // receives them.  The names are the properties' own (as the checker has them), however the
    // type spells them: `key`, `"key"`, `["key"]`, `k\u0065y`
    for (const s of m.checker.getPropertiesOfType(m.checker.getTypeFromTypeNode(p.type))) {
      const fname = s.getName();
      if (fname === "key") fail(p, `a prop named key: React uses key={…} to match list items and never passes it to the component (props.key is undefined); rename the prop (e.g. id)`);
      if (fname === "ref") fail(p, `a prop named ref: React 18 does not pass ref={…} to a function component (props.ref is undefined), and refs are not modelled; rename the prop`);
      if (RESERVED_PROPS.includes(fname)) fail(p, `a prop named ${fname}: ${RESERVED_WHY(fname)}; rename the prop`);
    }
    for (const f of m.reg.rec(propsType)) {
      if (f.type.k === "fn") {
        if (f.type.ret.k !== "void") fail(p, `callback ${f.name} must return void`);
        f.type.params.forEach((q) => checkValueType(p, q.type, m.reg, `parameter ${q.name} of callback ${f.name}`));
        callbacks.push({ name: f.name, params: f.type.params });
      } else if (f.type.k === "opt" && f.type.elem.k === "fn") {
        fail(p, `optional callback ${f.name} is not supported: make it required`);
      } else if (f.type.k === "node") {
        fail(p, `${f.name}: ReactNode props (children) are not supported yet`);
      } else {
        checkValueType(p, f.type, m.reg, `prop ${f.name}`);
        data.push(f);
      }
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
  /** the Lean locals `init` binds the initial values to when a later one reads an earlier state value */
  initNames: string[];
  /** whether an initial value reads a state value declared before it (`useState(a)`) */
  initReadsState: boolean;
  /**
   * The initial values that read an earlier state value and that React evaluates at every
   * render, not only at mount (all but a lazy `useState(() => …)`), at their types: also checked
   * in the render, with the state of that render (`translateComponent`).
   */
  renderChecks: { node: ts.Expression; type: VType }[];
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
        const fname = el.propertyName ? propertyName(el.propertyName) : el.name.text;
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
  // closures (handlers, effects, updaters, callbacks) over render-local `let`s must agree with JS;
  // of a @trusted component, in what is translated although its render is not (its contracts
  // and initial state: a block-bodied every/some callback there is read as code)
  checkClosures(body, env, info.trusted ? body.statements.filter((s) => prepassTranslates(s, env)) : undefined);
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
  // (a later initial value that reads an earlier state value reads its initial value: a local)
  const initBody = pp.initReadsState
    ? `${pp.inits.map((x, i) => `let ${pp.initNames[i]} : ${leanType(pp.stateVars[i].type)} := ${x};\n  `).join("")}State.mk${pp.initNames.map((x) => " " + x).join("")}`
    : `State.mk${pp.inits.map((x) => " " + paren(x)).join("")}`;
  out += `@[vreact_simp] def init (props : Props) (hpre : pre props) : State :=\n  ${initBody}\n\n`;
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
    // The Lean names of the state values are taken for the whole render (`lets`), but each state
    // value and setter is bound at its own declaration (`renderBlock`): before it, JS has it in
    // its temporal dead zone, so a function called there (a helper, an array callback, the
    // useMemo factory, a JSX const) that reads it throws a ReferenceError.
    const sc = new Set(renv.scope);
    for (const sv of pp.stateVars) sc.add(leanIdent(sv.name));
    renv = { ...renv, scope: sc };
    // an initial value that reads earlier state and that React evaluates at every render (its
    // value then unused): checked there too, against the state of the render (`stateVar`; it
    // reads only state declared before it)
    const allState = bindStateVars(renv, body.statements, pp.stateVars);
    for (const rc of pp.renderChecks) {
      const n0 = m.obligations.length;
      const v = expr(rc.node, { ...allState, limits: INIT_LIMITS }, rc.type);
      if (m.obligations.length > n0) lets += `let _ : ${leanType(rc.type)} := ${v.code};\n  `;
    }
    // (renderBlock attaches to each return the effects registered on its path)
    const bc: BlockCtx = {
      kind: "render",
      fnNode: fn,
      onReturn: (e, env2) => {
        if (!e) fail(fn, "components must return JSX or null");
        return jsxNode(e, env2);
      },
      jsxConst: jsxConstCtx(comp),
    };
    const renderBody = withBubble(NO_BUBBLE, () => renderBlock(pp.renderStmts, renv, bc, (c, env2) => effectCode(c, env2, info)));
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

/**
 * The hook call an initialiser or expression statement is, through parentheses
 * (`(useEffect(…))`, `const [n, setN] = (useState(0))`: the same call in JS), or null.
 */
function hookCall(e: ts.Expression | undefined): ts.CallExpression | null {
  if (!e) return null;
  const x = stripParens(e);
  return ts.isCallExpression(x) ? x : null;
}

/** Is `c` a call of useState / useReducer? */
function isStateHook(c: ts.CallExpression | null, env: Env): boolean {
  const h = c ? hookName(env, c.expression) : null;
  return h === "useState" || h === "useReducer";
}

/** Hooks VTS does not model (rejected wherever they are called). */
const UNMODELLED_HOOKS = new Set(["useRef", "useContext", "useLayoutEffect", "useSyncExternalStore", "useTransition", "useDeferredValue", "useId", "useImperativeHandle"]);

/** What the restricted environments of a component's contracts and initial values give access to (`Env.limits`). */
const PRE_LIMITS = "a requires(…) may mention only the props and top-level declarations (it is what every parent must establish before the component renders)";
const INV_LIMITS = "an invariant may mention only the props, the state and top-level declarations";
const CBREQ_LIMITS = "callbackRequires(…) may mention only the callback's arguments, the props and top-level declarations";
const INIT_LIMITS = "an initial value (useState / useReducer) may read only the props, the state values declared before it (at mount, their initial values) and top-level declarations";

/** Why the hook `h` is rejected: it is not modelled. */
function unmodelledHook(h: string): string {
  return `${h} is not modelled in VTS yet${h === "useLayoutEffect" ? " (its updates are synchronous, during the commit; use useEffect)" : ""}`;
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
      } else if (ts.isArrayBindingPattern(n.name) && isStateHook(hookCall(n.initializer), env)) {
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
      // (a shorthand property `{ f }` refers to the closure f)
      const sym = refSymbol(checker, n);
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

/** `env` with the state values and setters / dispatches declared by `stmts` bound. */
function bindStateVars(env: Env, stmts: readonly ts.Statement[], svs: StateVar[]): Env {
  let e = env;
  for (const s of stmts) {
    if (!ts.isVariableStatement(s)) continue;
    for (const d of s.declarationList.declarations) {
      const c = hookCall(d.initializer);
      if (!ts.isArrayBindingPattern(d.name) || !c) continue;
      const h = hookName(e, c.expression);
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

/**
 * Render statements: like `block`, plus useEffect handling.  `effect` translates a top-level
 * useEffect call in the environment where it runs.
 */
function renderBlock(stmts: ts.Statement[], env: Env, bc: BlockCtx, effect: (c: ts.CallExpression, env: Env) => string): string {
  // peel effects off at top level (they are hooks: unconditional, before returns).  A statement
  // before them may still branch without returning (`{ if (x !== null) { … } }`): the scan then
  // goes on once per path, and each path's returns carry the effects registered on that path,
  // each once and translated in that path's environment (its narrowings, its locals)
  const run = (i: number, e: Env, effects: readonly string[]): string => {
    if (i >= stmts.length) fail(bc.fnNode, "component must return");
    const s = stmts[i];
    const c = ts.isExpressionStatement(s) ? hookCall(s.expression) : null;
    if (c && hookName(e, c.expression) === "useEffect") return run(i + 1, e, [...effects, effect(c, e)]);
    // `const [n, setN] = useState(…)`: from here on `n` is this render's state value (its Lean
    // local is bound at the top of the render) and `setN` its setter
    if (ts.isVariableStatement(s) && isStateHook(hookCall(s.declarationList.declarations[0]?.initializer), e)) {
      return run(i + 1, bindStateVars(e, [s], e.comp!.stateVars), effects);
    }
    if (ts.isReturnStatement(s) && i < stmts.length - 1) fail(stmts[i + 1], "unreachable code after return (it never runs)");
    const pbc: BlockCtx = effects.length
      ? { ...bc, onReturn: (r, env2) => `(VReact.VNode.withEffects [${effects.join(",\n  ")}]\n  ${paren(bc.onReturn!(r, env2))})` }
      : bc;
    // translate this statement with a continuation that resumes the scan
    return block([s], 0, e, pbc, (e2) => run(i + 1, e2, effects));
  };
  return run(0, env, []);
}

function prepass(stmts: readonly ts.Statement[], env: Env, comp: CompCtx, m: ModCtx): Prepass {
  const pp: Prepass = { pre: [], inv: [], stateVars: [], inits: [], initNames: [], initReadsState: false, renderChecks: [], contracts: new Map(), renderStmts: [], propsEnv: env };
  let sawNonHook = false;
  let stateEnv: Env = { ...env, limits: INV_LIMITS }; // props + state (as σ.field) for invariants
  // the initial values: the props, and each state value declared so far bound to its own
  // initial value (`initNames`), which it has when React evaluates a later one at mount
  let initEnv: Env = { ...env, limits: INIT_LIMITS };
  const stateSyms: ts.Symbol[] = [];
  // several requires / invariants form one condition each, in order: a later one may use
  // the earlier ones as guards (`propAll`, as for function preconditions)
  const reqs: ts.Expression[] = [];
  const invs: ts.Expression[] = [];
  // for each invariant, how many state values are declared before it
  const invAt: number[] = [];
  for (const s of stmts) {
    const c = ts.isExpressionStatement(s) ? hookCall(s.expression) : null;
    if (c) {
      const sf = specFn(env, c.expression);
      if (sf === "requires" || sf === "invariant") {
        if (c.arguments.length !== 1) fail(c, `${sf}(condition)`);
        (sf === "requires" ? reqs : invs).push(c.arguments[0]);
        if (sf === "invariant") invAt.push(stateSyms.length);
        continue;
      }
      if (sf === "callbackRequires") {
        if (c.arguments.length !== 2) fail(c, "callbackRequires(cb, (args) => condition)");
        const cbE = c.arguments[0];
        const cb = contractCallback(cbE, env, comp);
        const lam = stripParens(c.arguments[1]);
        if (!(ts.isArrowFunction(lam) || ts.isFunctionExpression(lam))) fail(c, "callbackRequires(cb, (args) => condition)");
        // (parameter annotations are checked against the callback prop's parameter types; the
        // body is a contract proposition: JS never runs it)
        const l = contractLambda(lam, { ...env, limits: CBREQ_LIMITS }, cb.params.map((p) => p.type), fnParamTsTypes(m.checker.getTypeAtLocation(cbE), cbE, env) ?? cb.params.map(() => null));
        const prop = l.prop;
        const prev = pp.contracts.get(cb.name);
        if (!prev) pp.contracts.set(cb.name, { binders: l.binders, prop });
        else {
          // several contracts for one callback: all of them hold (conjunction), the
          // later one's parameters renamed to the first one's binders (simultaneously).  Both
          // have one binder per parameter of the callback; a parameter the earlier ones ignore
          // (`_`, which the later one would receive as a placeholder) is named after the later
          // one's binder, made distinct from the others (the earlier contracts do not mention it)
          const binders = [...prev.binders];
          l.binders.forEach((lb, i) => {
            if (binders[i] !== "_" || lb === "_") return;
            let nb = lb;
            for (let k = 1; binders.includes(nb); k++) nb = lb.endsWith("»") ? `${lb.slice(0, -1)}_${k}»` : `${lb}_${k}`;
            binders[i] = nb;
          });
          const same = l.binders.every((b, i) => b === binders[i]);
          const later = same ? paren(prop) : `((fun ${l.typed.join(" ")} => ${prop})${l.binders.map((_, i) => " " + binders[i]).join("")})`;
          pp.contracts.set(cb.name, { binders, prop: `${prev.prop} ∧ ${later}` });
        }
        continue;
      }
      if (sf) fail(c, `${sf}(…) is not allowed in a component body`);
      // a hook called as a statement at the top level (`(useEffect(…))` too): only useEffect
      const h = hookName(env, c.expression);
      if (h) {
        if (sawNonHook) fail(c, "hooks must run unconditionally before any early return (Rules of Hooks)");
        if (h === "useEffect") {
          pp.renderStmts.push(s);
          continue;
        }
        if (UNMODELLED_HOOKS.has(h)) fail(c, unmodelledHook(h));
        const bound = h === "useState" || h === "useReducer" ? `const [value, ${h === "useState" ? "setValue" : "dispatch"}] = ${h}(…)` : `const value = ${h}(…)`;
        fail(c, `${h}(…) as a statement (its value unused) is not supported: bind it (${bound})`);
      }
    }
    if (ts.isVariableStatement(s)) {
      // every declarator: `const x = 1, [n, setN] = useState(0)` declares a hook too
      for (const dd of s.declarationList.declarations) {
        const ddc = hookCall(dd.initializer);
        const hh = ddc ? hookName(env, ddc.expression) : null;
        if (hh && UNMODELLED_HOOKS.has(hh)) fail(dd, unmodelledHook(hh));
        if (hh === "useEffect") fail(dd, "useEffect(…) returns nothing: call it as a statement, useEffect(() => { … }, [deps]);");
        if ((hh === "useState" || hh === "useReducer") && s.declarationList.declarations.length !== 1) {
          fail(dd, `declare a ${hh} on its own (\`const [value, ${hh === "useState" ? "setValue" : "dispatch"}] = ${hh}(…);\`), not with other variables in one declaration`);
        }
      }
      const d = s.declarationList.declarations[0];
      const dc = hookCall(d?.initializer);
      const h = dc ? hookName(env, dc.expression) : null;
      if (dc && (h === "useState" || h === "useReducer")) {
        if (sawNonHook) fail(d, "hooks must run unconditionally before any early return (Rules of Hooks)");
        const sv = stateVar(d, dc, h, initEnv, m, pp, stateSyms);
        pp.stateVars.push(sv);
        const a = (d.name as ts.ArrayBindingPattern).elements[0] as ts.BindingElement;
        const sym = symbolOf(env, a.name)!;
        stateEnv = bind(stateEnv, sym, { k: "val", code: leanIdent(sv.name), type: sv.type });
        const r = freshLocal(initEnv, leanIdent(sv.name));
        initEnv = bind(r.env, sym, { k: "val", code: r.name, type: sv.type });
        pp.initNames.push(r.name);
        stateSyms.push(sym);
        // (kept in the render statements: the state value and setter are bound from here on)
        pp.renderStmts.push(s);
        continue;
      }
      // useMemo / useCallback: allowed only here (top level), before any early return
      for (const dd of s.declarationList.declarations) {
        const init = hookCall(dd.initializer);
        if (!init) continue;
        const h = hookName(env, init.expression);
        if (h !== "useMemo" && h !== "useCallback") continue;
        if (sawNonHook) fail(dd, "hooks must run unconditionally before any early return (Rules of Hooks)");
        topLevelHookDecls.add(dd);
      }
    }
    if (ts.isIfStatement(s) || ts.isReturnStatement(s) || ts.isSwitchStatement(s) || mayReturn(s)) sawNonHook = true;
    pp.renderStmts.push(s);
  }
  // An invariant may mention only the state declared before it: JS evaluates the argument of
  // `invariant(…)` where it stands, so a later state value is in its temporal dead zone there
  // (TypeScript rejects a direct read, not one inside a function: `forall(0, 1, (i) => b >= i)`).
  invs.forEach((inv, i) => {
    const later = stateSyms.slice(invAt[i]);
    const id = firstRead(inv, later, m.checker);
    if (id) {
      fail(id, `this invariant reads the state \`${id.text}\`, declared after it (${relLoc(refSymbol(m.checker, id)!.valueDeclaration!, m.prog.root)}): JS evaluates invariant(…)'s argument where it stands, and there \`${id.text}\` is in its temporal dead zone (a ReferenceError); move the invariant after the declaration`);
    }
  });
  if (reqs.length) pp.pre.push(propAll(reqs, { ...env, limits: PRE_LIMITS }));
  if (invs.length) pp.inv.push(propAll(invs, stateEnv));
  return pp;
}

/**
 * Does `prepass` translate (part of) this statement of a component body?  Its contracts
 * (`requires`, `invariant`, `callbackRequires`: any spec call, the others being rejected) and its
 * `useState` / `useReducer` declarations (the initial state).  For a @trusted component, whose
 * render is not translated, these are the statements `checkClosures` must cover.
 */
function prepassTranslates(s: ts.Statement, env: Env): boolean {
  if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression)) return !!specFn(env, s.expression.expression);
  if (ts.isVariableStatement(s)) {
    return s.declarationList.declarations.some((d) => {
      const init = d.initializer && stripParens(d.initializer);
      if (!init || !ts.isCallExpression(init)) return false;
      const h = hookName(env, init.expression);
      return h === "useState" || h === "useReducer";
    });
  }
  return false;
}

/**
 * The callback prop whose contract `callbackRequires(cbE, …)` states: the one `cbE` holds, by its
 * binding (as a call `cbE(…)` resolves it), never by its spelling — `props.onPick` on the props
 * parameter, or a name destructured from the props parameter (`{ onPick }`, `{ onPick: pick }`:
 * the local `pick` holds props.onPick).
 */
function contractCallback(cbE: ts.Expression, env: Env, comp: CompCtx): CallbackInfo {
  const form = `callbackRequires(cb, (args) => condition) states the contract of a callback prop of ${comp.info.name}: write cb as props.<name> (props being the props parameter) or as a name destructured from the props parameter`;
  const e = stripParens(cbE);
  if (ts.isIdentifier(e)) {
    const s = symbolOf(env, e);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "callback") return b.cb;
    if (b?.k === "props") fail(e, `\`${e.text}\` is the props object, not one of its callbacks: ${form}`);
    if (b?.k === "val") fail(e, `\`${e.text}\` holds a data prop of ${comp.info.name}, not a callback prop: ${form}`);
    fail(e, `\`${e.text}\` is not a name destructured from the props parameter of ${comp.info.name}: ${form}`);
  }
  if (ts.isPropertyAccessExpression(e) && !e.questionDotToken && ts.isIdentifier(e.expression)) {
    const s = symbolOf(env, e.expression);
    if (s && env.vars.get(s)?.k === "props") {
      const cb = comp.info.callbacks.find((x) => x.name === e.name.text);
      if (cb) return cb;
      fail(e, `props.${e.name.text} is not a callback prop of ${comp.info.name}: ${form}`);
    }
    fail(e, `\`${nodeText(e.expression)}\` is not the props parameter of ${comp.info.name}: ${form}`);
  }
  fail(e, `${form} (not \`${nodeText(e)}\`)`);
}

/** Does a statement of the component body contain a `return` of the component (not of a nested function)? */
function mayReturn(s: ts.Node): boolean {
  if (ts.isReturnStatement(s)) return true;
  if (ts.isFunctionLike(s) || ts.isClassLike(s)) return false;
  return !!ts.forEachChild(s, (c) => (mayReturn(c) ? true : undefined));
}

/**
 * A reducer's `requires` may constrain the action only. React keeps the dispatched action in the
 * hook's queue and passes that same value to every reducer call (rebasing, StrictMode replays),
 * so a fact about it, proved at the `dispatch(a)` site from the snapshot, holds at each of them.
 * The state argument is whatever queued state React applies the action to, which the
 * dispatching handler cannot see: facts about it belong in the component's invariant.
 */
function actionOnlyPre(r: FnInfo, env: Env) {
  const checker = env.m.checker;
  const stateSym = checker.getSymbolAtLocation(r.decl.parameters[0].name);
  const visit = (n: ts.Node): void => {
    const sym = ts.isShorthandPropertyAssignment(n) ? checker.getShorthandAssignmentValueSymbol(n) : ts.isIdentifier(n) ? checker.getSymbolAtLocation(n) : undefined;
    if (sym && sym === stateSym) {
      fail(n, `the reducer ${r.name}'s requires(…) may mention only the action, not the state ${r.params[0].name}: React may apply a queued action to any state, so it is checked at each dispatch from the action alone (put facts about the state in the component's invariant)`);
    }
    ts.forEachChild(n, visit);
  };
  for (const s of r.decl.body?.statements ?? []) {
    if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && specFn(env, s.expression.expression) === "requires") visit(s.expression);
  }
}

/** Does `n` refer to one of the variables `syms` (also as a shorthand property `{ a }`)? */
function readsAny(n: ts.Node, syms: readonly ts.Symbol[], checker: ts.TypeChecker): boolean {
  return !!firstRead(n, syms, checker);
}

/** The first identifier in `n` that refers to one of the variables `syms` (also as a shorthand property `{ a }`), or null. */
function firstRead(n: ts.Node, syms: readonly ts.Symbol[], checker: ts.TypeChecker): ts.Identifier | null {
  if (!syms.length) return null;
  if (ts.isIdentifier(n)) {
    const s = refSymbol(checker, n);
    if (s && syms.includes(s)) return n;
  }
  return ts.forEachChild(n, (c) => firstRead(c, syms, checker) ?? undefined) ?? null;
}

/**
 * A `useState` / `useReducer` slot, its initial value translated in `env`: the props, and the
 * state values declared before it (`earlier`) bound to their initial values.  React evaluates
 * the argument `init` in the render (`useState(a)` reads the state `a` of that render) and uses it
 * only at mount, when every earlier state value is its initial value: so `init` has the value
 * it is translated to here.  An argument evaluated at every render that reads earlier state is
 * also checked in the render, against the state there (`renderChecks`): its value is discarded
 * then, but JS still evaluates it.
 */
function stateVar(d: ts.VariableDeclaration, c: ts.CallExpression, h: string, env: Env, m: ModCtx, pp: Prepass, earlier: readonly ts.Symbol[]): StateVar {
  if (!ts.isArrayBindingPattern(d.name) || d.name.elements.length < 1) fail(d, `use const [value, setValue] = ${h}(…)`);
  const a = d.name.elements[0];
  if (!ts.isBindingElement(a) || !ts.isIdentifier(a.name)) fail(d, "state variable must be an identifier");
  const name = a.name.text;
  if (h === "useState") {
    let t: VType | undefined = c.typeArguments?.[0] ? typeOfNode(c.typeArguments[0], m.prog.typeEnv, name[0].toUpperCase() + name.slice(1)) : undefined;
    if (t) checkValueType(c.typeArguments![0], t, m.reg, `state \`${name}\``);
    const init = c.arguments[0];
    if (!init) fail(c, "useState needs an initial value");
    let v;
    const ii = ts.isParenthesizedExpression(init) ? init.expression : init;
    const reads = readsAny(init, earlier, m.checker);
    if (ts.isArrowFunction(ii) && ii.parameters.length === 0) {
      // (a lazy initialiser: React calls it at mount only)
      v = ts.isBlock(ii.body) ? valueBlock(ii.body.statements, env, t, ii) : expr(ii.body, env, t);
    } else v = expr(init, env, t);
    t = t ?? v.type;
    if (reads) {
      pp.initReadsState = true;
      if (!(ts.isArrowFunction(ii) && ii.parameters.length === 0)) pp.renderChecks.push({ node: init, type: t });
    }
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
  if (r.tparams.length) fail(rId, `a generic function (${r.name}<${r.tparams.map((p) => p.name).join(", ")}>) cannot be a reducer: React calls it with no type arguments; write a reducer with concrete state and action types (it may call the generic function)`);
  if (r.params.length !== 2) fail(rId, "a reducer takes (state, action)");
  if (r.hasPre) actionOnlyPre(r, env);
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
    if (readsAny(c.arguments[1], earlier, m.checker)) {
      pp.initReadsState = true;
      pp.renderChecks.push({ node: c.arguments[1], type: st });
    }
  }
  pp.inits.push(initCode!);
  return { name, field: name, type: st, reducer: r, actionType: r.params[1].type };
}

/* ───────────────────────────── effects ───────────────────────────── */

/**
 * The dependency values (`VReact.DepVal`) that the effect dependency `d` (translated in `env`)
 * contributes; React compares each entry with `Object.is` to the previous render's. A data value by
 * its type (a number, array, record, Map or optional: `obj`, whose `Object.is` the model does not
 * decide — the run chooses whether the effect runs again, `depsChanged`; effects are robust, so
 * either choice is verified, SEMANTICS §2.6); a setter or `dispatch`: none (React keeps one
 * function per hook, so it never changes); a local arrow: `obj` (a new function at every render:
 * in React the effect runs after every render, one of the model's choices); a
 * `useCallback` function: the values of its own dependencies (React returns the cached function
 * until one of them changes, so it changes when they do); a JSX const: `obj` (a new element object
 * at every render); a path that starts at a top-level declaration of the program (a function,
 * constant or component, or an import of one): none (created once, when its module is evaluated —
 * top-level variables are const — so the same value at every render), and so is `undefined`; a
 * path that starts at anything else declared outside the component (a global such as `Math`):
 * rejected, with that reason (the dependency check never requires one; `innerWidth` would
 * change); a parent callback: rejected (an effect never calls one, and when the parent passes a
 * new function is not modelled), and so is the props object (its fields are the dependencies).
 * `at` is the effect's dependency `d` comes from, `via` the useCallback it was reached through.
 */
function effectDepVals(d: ts.Expression, env: Env, at: ts.Expression, via: string | null): string[] {
  const e = stripParens(d);
  const s = ts.isIdentifier(e) ? symbolOf(env, e) : undefined;
  const b = s ? env.vars.get(s) : undefined;
  const propsCb = (x: ts.Expression): boolean => {
    if (!ts.isPropertyAccessExpression(x) || !ts.isIdentifier(x.expression)) return false;
    const ps = symbolOf(env, x.expression);
    return !!ps && env.vars.get(ps)?.k === "props" && !env.comp!.info.data.some((f) => f.name === x.name.text);
  };
  if (b?.k === "callback" || propsCb(e)) {
    const why = "an effect never calls parent callbacks, and when the parent passes a new function is not modelled";
    if (via) fail(at, `the effect depends on ${via}, a useCallback function whose dependency \`${nodeText(e)}\` is a parent callback: not supported as an effect dependency (${why})`);
    fail(at, `\`${nodeText(e)}\` is a parent callback: it cannot be an effect dependency (${why})`);
  }
  if (b?.k === "props") {
    const what = "the props object is not an effect dependency: list the fields the effect reads (props.x)";
    if (via) fail(at, `the effect depends on ${via}, a useCallback function that lists the props object: ${what}`);
    fail(at, what);
  }
  if (b?.k === "setter" || b?.k === "dispatch") return [];
  if (b?.k === "closure") {
    const call = b.fn.parent;
    if (ts.isCallExpression(call) && call.arguments[0] === b.fn && hookName(b.env, call.expression) === "useCallback") {
      const deps = call.arguments[1];
      // (checkDeps checked an array literal at the declaration)
      if (!deps || !ts.isArrayLiteralExpression(deps)) fail(at, "useCallback needs a dependency array");
      return deps.elements.flatMap((x) => effectDepVals(x, b.env, at, via ?? `\`${nodeText(e)}\``));
    }
    return ["VReact.DepVal.obj"];
  }
  if (b?.k === "jsx") return ["VReact.DepVal.obj"];
  // the variable the path starts with, when it is declared outside the component
  let root: ts.Expression = e;
  while (ts.isPropertyAccessExpression(root) || ts.isParenthesizedExpression(root)) root = root.expression;
  const rs = ts.isIdentifier(root) ? symbolOf(env, root) : undefined;
  if (rs && !env.vars.has(rs)) {
    // (and `undefined`, a non-writable global: always the same value)
    if (globalOf(env, root) || (root === e && isGlobal(env, root, "undefined"))) return [];
    const decl = env.comp!.info.decl;
    const inComp = (x: ts.Node): boolean => {
      for (let n: ts.Node | undefined = x; n; n = n.parent) if (n === decl) return true;
      return false;
    };
    const ds = rs.declarations ?? [];
    if (ds.length && !ds.some(inComp)) {
      const what = `${root === e ? "is" : `starts at \`${nodeText(root)}\`,`} declared outside the component, and not a top-level declaration of the program (a function, constant or component)`;
      const why = `not supported as an effect dependency; the dependency check never requires a value from outside the component: leave it out`;
      if (via) fail(at, `the effect depends on ${via}, a useCallback function whose dependency \`${nodeText(e)}\` ${what}: ${why} (of ${via}'s dependencies)`);
      fail(at, `\`${nodeText(e)}\` ${what}: ${why}`);
    }
  }
  const v = expr(d, env);
  switch (v.type.k) {
    case "int":
      return [`VReact.DepVal.int ${paren(v.code)}`];
    case "str":
      return [`VReact.DepVal.str ${paren(v.code)}`];
    case "bool":
      return [`VReact.DepVal.bool ${paren(v.code)}`];
    case "enum":
      return [`VReact.DepVal.str (VReact.JS.str ${paren(v.code)})`];
    default:
      return [`VReact.DepVal.obj`];
  }
}

function effectCode(c: ts.CallExpression, env: Env, info: CompInfo): string {
  const m = env.m;
  const fn = c.arguments[0];
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length) fail(c, "useEffect(() => { … }, [deps])");
  if (fn.modifiers?.some((x) => x.kind === ts.SyntaxKind.AsyncKeyword)) fail(fn, "async effects are not supported");
  checkDeps(fn, c.arguments[1], env, "useEffect");
  // deps
  let deps = "none";
  if (c.arguments[1] && ts.isArrayLiteralExpression(c.arguments[1])) {
    const ds = c.arguments[1].elements.flatMap((d) => effectDepVals(d, env, d, null));
    deps = `some [${ds.join(", ")}]`;
  }
  // split the body into: synchronous statements, timer registrations (tasks), cleanup
  let stmts = ts.isBlock(fn.body) ? [...fn.body.statements] : [ts.factory.createExpressionStatement(fn.body)];
  let bodyE: ts.Node = fn.body;
  while (ts.isParenthesizedExpression(bodyE)) bodyE = bodyE.expression;
  /** useEffect(() => () => cleanup): the cleanup is created at once */
  const cleanupOnly = ts.isArrowFunction(bodyE) || ts.isFunctionExpression(bodyE) ? bodyE : null;
  if (cleanupOnly) stmts = [];
  // an expression body is the effect's return value, which React keeps as the cleanup and
  // calls (unless it is undefined) before the next run and on unmount: a timer id or an
  // assigned value there would throw a TypeError then
  else if (!ts.isBlock(fn.body) && !returnsUndefined(fn.body, env)) {
    fail(fn.body, `the value of \`${nodeText(fn.body, 40)}\` is the effect's return value, which React calls as its cleanup (a TypeError when it is not a function); write the effect body in braces: useEffect(() => { ${nodeText(fn.body, 30)}; }, …)`);
  }
  const tasks: string[] = [];
  /** the registration `setTimeout(cb, delay)` of each timer statement */
  const timerCalls = new Map<ts.Statement, ts.CallExpression>();
  const timerCall = (e: ts.Expression): ts.CallExpression | null => {
    e = stripParens(e);
    if (ts.isCallExpression(e) && (isGlobal(env, e.expression, "setInterval") || isGlobal(env, e.expression, "setTimeout"))) return e;
    return null;
  };
  stmts.forEach((s, i) => {
    // JS does not run what follows a top-level `return` (the model must not either)
    if (ts.isReturnStatement(s) && i < stmts.length - 1) fail(stmts[i + 1], "unreachable code after return (it never runs)");
    let call: ts.CallExpression | null = null;
    if (ts.isExpressionStatement(s)) call = timerCall(s.expression);
    if (ts.isVariableStatement(s) && s.declarationList.declarations.length === 1 && s.declarationList.declarations[0].initializer) {
      call = timerCall(s.declarationList.declarations[0].initializer!);
    }
    if (call) {
      if (!call.arguments.length) fail(call, `${nodeText(call.expression)} needs a callback`);
      if (call.arguments.length > 2) fail(call.arguments[2], `extra arguments of ${nodeText(call.expression)} are passed to its callback: not supported (use them in the callback directly)`);
      // the delay: data only (it is also translated, with its obligations, where the timer is
      // registered: `onStmt`)
      if (call.arguments[1]) pureCleanupExpr(call.arguments[1], env, TIMER_ARG_RULE, "a timer's delay");
      const timer = call.arguments[0];
      tasks.push(`(fun _ => ${timerTask(stmts.slice(0, i), 0, env, fn, timerCalls, timer, (e) => handlerFn(timer, e, "robust", []).code)})`);
      timerCalls.set(s, call);
      return;
    }
  });
  // the synchronous part, translated as a robust handler body; a timer registration evaluates
  // its delay there (its callback is a task), and `return cleanup` the cleanup's arguments
  const acc = { kind: "robust" as const, updates: [], emit: null, eventVar: null };
  const e1: Env = { ...env, handler: acc, curState: undefined };
  const done = (e3: Env) => outcome(e3.handler!, env.comp!);
  const onStmt = (s: ts.Statement, e: Env, rest: (e: Env) => string): string | null => {
    const call = timerCalls.get(s);
    if (!call) return null;
    const delay = call.arguments[1];
    if (delay && !isNumeric(typeOf(delay, e))) fail(delay, "the delay of a timer must be a number");
    // `const id = setTimeout(…)`: the handle exists from here on (before, it is in its temporal
    // dead zone, also for a cleanup returned earlier on another path)
    const handle = (e2: Env): Env => {
      if (!ts.isVariableStatement(s)) return e2;
      const d = s.declarationList.declarations[0];
      if (!(s.declarationList.flags & ts.NodeFlags.Const)) fail(s, `declare the timer handle with const: const ${nodeText(d.name)} = ${nodeText(call.expression)}(…)`);
      if (!ts.isIdentifier(d.name)) fail(d.name, "a timer handle is bound to a name: const id = setTimeout(…)");
      return bind(e2, symbolOf(e2, d.name)!, { k: "timer" });
    };
    return evalArgs(delay ? [delay] : [], e, (e2) => rest(handle(e2)));
  };
  const onCleanup = (c: ts.Expression, e: Env): string => `(let _ : Unit := ${cleanupCode(c, e)};\n${done(e)})`;
  const setup = cleanupOnly ? onCleanup(cleanupOnly, e1) : block(stmts, 0, e1, { kind: "handler", fnNode: fn, onDone: done, onCleanup, onStmt }, done);
  const okSetup = m.ob(c, "effect-robust", `effect at ${nodeText(c, 40)} preserves the invariant of ${info.name} from any state (effects may run with stale snapshots)`);
  const okTasks = tasks.length
    ? m.ob(c, "effect-robust", `timer callbacks of the effect preserve the invariant of ${info.name} from any state`)
    : `(/-⟦gen⟧-/ by simp)`;
  return `(VReact.Effect.mk (S := ${info.ns}.State) (E := E) (inv := ${info.ns}.inv props) (${deps}) ${paren(setup)} ${okSetup}\n     (/-⟦gen⟧-/ by vreact_noemit)\n     [${tasks.join(", ")}] ${okTasks})`;
}

/**
 * Does the expression statement `e` certainly evaluate to undefined?  Calls of setters and
 * dispatch, external writes (`console.*`, `localStorage.setItem`), and local helpers whose
 * body returns no value.
 */
function returnsUndefined(e0: ts.Expression, env: Env): boolean {
  const e = stripParens(e0);
  if (!ts.isCallExpression(e)) return false;
  if (ts.isPropertyAccessExpression(e.expression)) return isGlobal(env, e.expression.expression, "console") || (e.expression.name.text === "setItem" && isGlobal(env, e.expression.expression, "localStorage"));
  if (!ts.isIdentifier(e.expression)) return false;
  const s = symbolOf(env, e.expression);
  const b = s ? env.vars.get(s) : undefined;
  if (b?.k === "setter" || b?.k === "dispatch") return true;
  if (b?.k !== "closure") return false;
  const body = b.fn.body;
  if (!ts.isBlock(body)) return returnsUndefined(body, b.env);
  let value = false;
  const visit = (n: ts.Node) => {
    if (ts.isReturnStatement(n) && n.expression && !isUndefinedReturn(n.expression, b.env)) value = true;
    if (!ts.isFunctionLike(n)) ts.forEachChild(n, visit);
  };
  body.statements.forEach(visit);
  return !value;
}

/**
 * A condition that held when the effect body went past a top-level statement: an
 * early return `if (c) return;` (no `else`) leaves `!c`; `assert(c)` (proved where it
 * stands) and `assume(c)` (assumed, and reported) leave `c`.
 */
interface TimerGuard {
  cond: ts.Expression;
  holds: boolean;
}

function timerGuard(s: ts.Statement, env: Env): TimerGuard | null {
  if (ts.isIfStatement(s) && !s.elseStatement) {
    const t = s.thenStatement;
    // (`return undefined;` is `return;`: no cleanup)
    const bare = (x: ts.Statement) => ts.isReturnStatement(x) && (!x.expression || isUndefinedReturn(x.expression, env));
    if (bare(t) || (ts.isBlock(t) && t.statements.length === 1 && bare(t.statements[0]))) return { cond: s.expression, holds: false };
    return null;
  }
  if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && s.expression.arguments.length === 1) {
    const f = specFn(env, s.expression.expression);
    if (f === "assert" || f === "assume") return { cond: s.expression.arguments[0], holds: true };
  }
  return null;
}

/**
 * A timer callback (`body`), translated in the environment of the effect body at its
 * registration and checked under the path condition there.  `items` are the effect body's
 * top-level statements before the registration (`env`: the component's environment at the
 * `useEffect`).  The callback captures the same snapshot as the effect: an effect cannot assign
 * a variable it captures, and a captured `let` is not reassigned after the effect is created.
 * * A guard (top-level early return, assert, assume: `timerGuard`) holds whenever the timer is
 *   registered, so the callback is `if h : c then body else skip` (or the reverse): the skip
 *   branch is a timer the real program never registers, and does nothing, which preserves every
 *   invariant.  A guard is used only if it translates here without obligations of its own (those
 *   stay with the effect body); others are left out, which only weakens the timer's facts.
 * * A top-level `const` that the callback or another statement refers to is bound to its
 *   value by translating its declaration again here, as
 *   the effect body does: it is evaluated once, before the registration, from the snapshot and
 *   the effect's earlier consts, and keeps that value (a local Map / Set the effect mutates
 *   afterwards is not bound).  Only a declaration that translates without obligations of its own
 *   (those stay with the effect body) is bound; the others, the `let`s and the timer handles
 *   are recorded in `env.unavailable`, for the message if the callback reads them.
 */
function timerTask(items: readonly ts.Statement[], i: number, env: Env, fn: ts.Node, timerCalls: ReadonlyMap<ts.Statement, ts.CallExpression>, cb: ts.Expression, body: (e: Env) => string): string {
  if (i === items.length) return body(env);
  const s = items[i];
  const m = env.m;
  const next = (e: Env) => timerTask(items, i + 1, e, fn, timerCalls, cb, body);
  const g = timerGuard(s, env);
  if (g) {
    let usable = false;
    m.dryRun(() => {
      const n0 = m.obligations.length;
      try {
        branch(g.cond, env, () => "true", () => "false");
        usable = m.obligations.length === n0;
      } catch (err) {
        if (!(err instanceof VtsError)) throw err;
      }
    });
    if (!usable) return next(env);
    const skip = outcome({ kind: "robust", updates: [], emit: null, eventVar: null }, env.comp!);
    return g.holds ? branch(g.cond, env, next, () => skip) : branch(g.cond, env, () => skip, next);
  }
  if (!ts.isVariableStatement(s)) return next(env);
  const names = boundNames(s.declarationList);
  // (a declaration that neither the callback nor another statement refers to is left out; an
  // earlier one can only through a local function, which may run after it)
  const syms = names.map((n) => symbolOf(env, n)).filter((x): x is ts.Symbol => !!x);
  if (![cb, ...items.filter((_, j) => j !== i)].some((n) => readsAny(n, syms, m.checker))) return next(env);
  const unavailable = (why: (name: string) => string): Env => {
    const u = new Map(env.unavailable ?? []);
    for (const n of names) {
      const sym = symbolOf(env, n);
      if (sym) u.set(sym, why(n.text));
    }
    return { ...env, unavailable: u };
  };
  if (timerCalls.has(s)) return next(unavailable((x) => `\`${x}\` is a timer handle: it can only be cleared, with clearTimeout(${x}) / clearInterval(${x}) in the effect's cleanup`));
  if (!(s.declarationList.flags & (ts.NodeFlags.Const | ts.NodeFlags.Let))) return next(unavailable(() => "use const or let (no var)"));
  if (!(s.declarationList.flags & ts.NodeFlags.Const)) {
    return next(unavailable((x) => `\`${x}\` is a \`let\` of the effect body: VTS binds in a timer callback only the effect body's \`const\`s declared before the registration, computed from the props, the state and earlier such consts`));
  }
  if (s.declarationList.declarations.some((d) => isMutatedLocal(d))) {
    return next(unavailable((x) => `\`${x}\` is a Map or Set the effect body mutates: VTS binds in a timer callback only the effect body's \`const\`s that keep the value of their declaration`));
  }
  // the declaration, translated as the effect body translates it (a robust handler body)
  const acc = { kind: "robust" as const, updates: [], emit: null, eventVar: null };
  const eh: Env = { ...env, handler: acc, curState: undefined };
  const bc: BlockCtx = { kind: "handler", fnNode: fn, onDone: () => fail(s, "internal: a declaration has no outcome") };
  let why: string | null = null;
  m.dryRun(() => {
    const n0 = m.obligations.length;
    try {
      block([s], 0, eh, bc, () => "()");
      if (m.obligations.length !== n0) why = "its value has proof obligations of its own (they are checked in the effect body, not repeated in the callback); compute it in the callback instead";
    } catch (err) {
      if (!(err instanceof VtsError)) throw err;
      why = err.message;
    }
  });
  if (why !== null) {
    const reason = why;
    return next(unavailable((x) => `\`${x}\` is a const of the effect body that VTS cannot bind in a timer callback: ${reason}`));
  }
  return block([s], 0, eh, bc, (e2) => next({ ...e2, handler: env.handler, curState: env.curState }));
}

/** The identifiers a declaration list binds (through destructuring patterns). */
function boundNames(l: ts.VariableDeclarationList): ts.Identifier[] {
  const out: ts.Identifier[] = [];
  const visit = (n: ts.BindingName) => {
    if (ts.isIdentifier(n)) out.push(n);
    else for (const el of n.elements) if (!ts.isOmittedExpression(el)) visit(el.name);
  };
  for (const d of l.declarations) visit(d.name);
  return out;
}

const TIMER_ARG_RULE = "the delay of setTimeout/setInterval must be data (a literal, a constant, props or state, pure functions of them): no mutating methods (push, sort, set, …), casts, `arguments`, `any`, setters or helpers";
const CLEANUP_RULE = "effect cleanups may only clear timers (clearTimeout/clearInterval) and make external writes (console.*, localStorage.*, document.title = …), possibly under if/else: React runs a cleanup later, with the props and state of the render that created it, and the cleanup is not verified";

/**
 * An effect cleanup.  The model has no cleanup step, so a cleanup must not be able to affect
 * any component state: only timer clearing and the documented external writes, whose
 * arguments are pure expressions, possibly under `if`/`else` with a pure condition.
 * Setters, dispatch, parent callbacks and local helpers (which may reach them) are rejected,
 * directly or nested.  JS still evaluates its conditions and arguments when it runs, which
 * may throw (`xs[9].name`, `x!.f`) or call a function outside its precondition; it runs with
 * the values it captured — those at the effect's `return` (`env`): a captured `let` is never
 * reassigned after the cleanup is created (`checkClosures`), and the effect's own statements
 * end with the `return`.  So they are translated here, with their obligations, into a `Unit`
 * term evaluated at the `return`.
 */
function cleanupCode(e0: ts.Expression, env: Env): string {
  const e = stripParens(e0);
  if (!ts.isArrowFunction(e) && !ts.isFunctionExpression(e)) fail(e0, `an effect cleanup must be an inline function \`() => { … }\`; ${CLEANUP_RULE}`);
  if (e.parameters.length) fail(e, "effect cleanups take no parameters");
  if (e.asteriskToken || e.modifiers?.some((x) => x.kind === ts.SyntaxKind.AsyncKeyword)) fail(e, `an effect cleanup must be a plain function (not async or a generator); ${CLEANUP_RULE}`);
  const items = ts.isBlock(e.body) ? [...e.body.statements] : [e.body];
  checkCleanupItems(items, env);
  return cleanupItems(items, 0, env, () => "()");
}

/** The evaluation of cleanup statements (already checked by `checkCleanupItems`), then `k`. */
function cleanupItems(items: readonly ts.Node[], i: number, env: Env, k: (e: Env) => string): string {
  if (i >= items.length) return k(env);
  const it = items[i];
  const next = (e: Env) => cleanupItems(items, i + 1, e, k);
  if (ts.isEmptyStatement(it)) return next(env);
  if (ts.isBlock(it)) return cleanupItems(it.statements, 0, env, next);
  if (ts.isIfStatement(it)) {
    const els = it.elseStatement;
    const onTrue = (e: Env) => cleanupItems([it.thenStatement], 0, e, next);
    const onFalse = (e: Env) => (els ? cleanupItems([els], 0, e, next) : next(e));
    const known = timerHandleTest(it.expression, env);
    if (known !== null) return known ? onTrue(env) : onFalse(env);
    return branch(it.expression, env, onTrue, onFalse);
  }
  const x = stripParens(ts.isExpressionStatement(it) ? it.expression : (it as ts.Expression));
  if (ts.isCallExpression(x)) {
    // clearTimeout(id) of a timer the effect registered: reading the handle cannot fail
    if (ts.isIdentifier(x.expression) && x.arguments.length === 1 && timerHandle(x.arguments[0], env)) return next(env);
    return evalArgs(x.arguments, env, next);
  }
  if (ts.isBinaryExpression(x)) return evalArgs([x.right], env, next); // document.title = …
  fail(it, CLEANUP_RULE);
}

/**
 * `id`: a timer handle, the `const` an effect binds to `setTimeout(…)` / `setInterval(…)` (not
 * a VTS value): a positive integer in browsers, never null, undefined or 0.  It exists only once
 * the registration has run on the path to the cleanup's `return` (`env` binds it then, as
 * `{ k: "timer" }`); a cleanup returned earlier — from a branch before `const id = …` — reads
 * it in its temporal dead zone when React calls it, which throws a ReferenceError.
 */
function timerHandle(x0: ts.Expression, env: Env): boolean {
  const x = stripParens(x0);
  if (!ts.isIdentifier(x)) return false;
  const s = symbolOf(env, x);
  if (!s) return false;
  const b = env.vars.get(s);
  if (b) return b.k === "timer";
  const d = s.valueDeclaration;
  if (!d || !ts.isVariableDeclaration(d) || !d.initializer) return false;
  const init = stripParens(d.initializer);
  const reg = ts.isCallExpression(init) && ts.isIdentifier(init.expression) && ["setTimeout", "setInterval"].includes(init.expression.text) && isGlobal(env, init.expression, init.expression.text);
  if (reg) fail(x, `the cleanup reads \`${x.text}\` before \`const ${x.text} = ${init.expression.text}(…)\` has run on this path: when React calls the cleanup, \`${x.text}\` is still in its temporal dead zone and reading it throws a ReferenceError. Return this cleanup only after registering the timer, or do not clear it on this path`);
  return false;
}

/** The value of a condition on a timer handle (`id !== null`, `id`, `!id`), or null if it is not one. */
function timerHandleTest(c0: ts.Expression, env: Env): boolean | null {
  const c = stripParens(c0);
  if (ts.isPrefixUnaryExpression(c) && c.operator === ts.SyntaxKind.ExclamationToken) {
    const v = timerHandleTest(c.operand, env);
    return v === null ? null : !v;
  }
  if (timerHandle(c, env)) return true;
  if (!ts.isBinaryExpression(c)) return null;
  const op = c.operatorToken.kind;
  const ops = [ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken];
  if (!ops.includes(op)) return null;
  const nullish = (e: ts.Expression) => {
    const x = stripParens(e);
    return isNullLit(x, env);
  };
  if (!((timerHandle(c.left, env) && nullish(c.right)) || (timerHandle(c.right, env) && nullish(c.left)))) return null;
  return op === ts.SyntaxKind.ExclamationEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken;
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
      // of the globals (a local or parameter named `console` or `clearTimeout` is not one)
      const timerClear = isGlobal(env, callee, "clearTimeout") || isGlobal(env, callee, "clearInterval");
      const external = ts.isPropertyAccessExpression(callee) && (isGlobal(env, unparen(callee.expression), "console") || isGlobal(env, unparen(callee.expression), "localStorage"));
      if (timerClear || external) {
        x.arguments.forEach((a) => pureCleanupExpr(a, env));
        continue;
      }
    }
    if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.EqualsToken && isDocumentTitle(x.left, env)) {
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

function unparen(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  return e;
}

/** Map/Set methods that only read (`size` is a property). */
const COLLECTION_READS = new Set(["get", "has", "keys", "values", "entries"]);

/**
 * The library methods that only read their receiver and arguments, by the interface that
 * declares them (TypeScript's lib): array methods other than the mutators, string, number and
 * boolean methods, `Math.*`, `JSON.stringify`, Map/Set reads and `Object.prototype`'s.  A
 * function they call is an inline callback, checked like the rest.  Not mutators (`xs.push`,
 * `m.get(k)!.push`, `m.set`), not `.call` / `.apply` / `.bind` (which run any function:
 * `Array.prototype.push.call(xs, …)`), not DOM or storage methods, not props callbacks.
 */
const PURE_LIB_METHODS: ReadonlyMap<string, (name: string) => boolean> = new Map([
  ["Array", (name: string) => !ARRAY_MUTATORS.has(name)],
  ["ReadonlyArray", () => true],
  ["String", () => true],
  ["Number", () => true],
  ["Boolean", () => true],
  ["Math", () => true],
  ["JSON", (name: string) => name === "stringify"],
  ["Map", (name: string) => COLLECTION_READS.has(name)],
  ["ReadonlyMap", (name: string) => COLLECTION_READS.has(name)],
  ["Set", (name: string) => COLLECTION_READS.has(name)],
  ["ReadonlySet", (name: string) => COLLECTION_READS.has(name)],
  ["Object", (name: string) => ["toString", "toLocaleString", "valueOf", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable"].includes(name)],
]);

/** Is `callee` (`recv.m`) a library method that only reads (see PURE_LIB_METHODS)? */
function isPureLibMethod(callee: ts.PropertyAccessExpression, env: Env): boolean {
  const sym = env.m.checker.getSymbolAtLocation(callee.name);
  const ds = sym?.declarations;
  if (!sym || !ds?.length || !isLibSymbol(sym, env.m.prog.typeEnv)) return false;
  return ds.every((d) => {
    const owner = d.parent;
    const ok = owner && ts.isInterfaceDeclaration(owner) ? PURE_LIB_METHODS.get(owner.name.text) : undefined;
    return !!ok && ok(callee.name.text);
  });
}

/** Is `id` the name a declaration introduces (a parameter, variable, property key, member access `a.x`, …)? */
function isDeclName(id: ts.Identifier): boolean {
  const p = id.parent as ts.Node & { name?: ts.Node; label?: ts.Node };
  if (ts.isLabeledStatement(p) || ts.isBreakOrContinueStatement(p)) return p.label === id;
  const named = ts.isPropertyAccessExpression(p) || ts.isParameter(p) || ts.isVariableDeclaration(p) || ts.isBindingElement(p) || ts.isPropertyAssignment(p) || ts.isFunctionExpression(p) || ts.isFunctionDeclaration(p) || ts.isClassExpression(p) || ts.isClassDeclaration(p) || ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p) || ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p) || ts.isJsxAttribute(p);
  return named && p.name === id;
}

/** Does a value of this type have call or construct signatures (a function, a class)? */
function isFunctionValued(t: ts.Type, env: Env): boolean {
  const ck = env.m.checker;
  return (t.isUnion() ? t.types : [t]).some((p) => ck.getSignaturesOfType(p, ts.SignatureKind.Call).length > 0 || ck.getSignaturesOfType(p, ts.SignatureKind.Construct).length > 0);
}

/**
 * Code that JS evaluates but VTS does not translate — the arguments and conditions inside an
 * effect cleanup, a timer's delay: data only.  Calls only of pure library methods (see
 * PURE_LIB_METHODS), `String(…)`, vreact/spec functions and the module's functions, with no
 * function passed to them other than an inline callback (`[1].map(setN)` would call the setter);
 * no state updates, callbacks, helpers, assignments, `new`, `delete`, `await`, tagged templates,
 * casts, `arguments` or `any`.
 */
function pureCleanupExpr(n: ts.Node, env: Env, rule = CLEANUP_RULE, who = "effect cleanups") {
  const call = (x: ts.CallExpression) => {
    const callee = unparen(x.expression);
    let ok = false;
    if (ts.isIdentifier(callee)) {
      const s = symbolOf(env, callee);
      const d = s && (s.flags & ts.SymbolFlags.Alias ? env.m.checker.getAliasedSymbol(s) : s).declarations?.[0];
      ok = !env.vars.get(s!) && (isGlobal(env, callee, "String") || !!specFn(env, callee) || (!!d && env.m.prog.globals.get(d)?.k === "fn"));
    } else if (ts.isPropertyAccessExpression(callee)) {
      // (a verified function through a module namespace, `L.f(…)`, is the module's function f)
      ok = isPureLibMethod(callee, env) || nsMember(env, callee)?.g?.k === "fn";
    }
    if (!ok) {
      const mut = ts.isPropertyAccessExpression(callee) && (ARRAY_MUTATORS.has(callee.name.text) || ["set", "add", "delete", "clear"].includes(callee.name.text)) ? ` (it mutates ${nodeText(callee.expression, 30)})` : "";
      fail(x, `${who} may not call \`${nodeText(callee, 40)}\` here${mut}; ${rule}`);
    }
  };
  /**
   * A function value used other than by calling it here: passed (`[1].map(setN)`), stored
   * (`{ toString: setN }`, `{ toJSON }`, `[setN]`) or chosen (`c ? f : g`) — the code it goes
   * to may call it (`String(…)` calls `toString`, `JSON.stringify` `toJSON`).  An inline
   * function is checked itself, and a method by the call it is the callee of.
   */
  const fnRef = (x: ts.Node) => {
    const ck = env.m.checker;
    let t: ts.Type | undefined;
    if (ts.isIdentifier(x)) {
      const p = x.parent;
      if (ts.isShorthandPropertyAssignment(p) && p.name === x) {
        const v = ck.getShorthandAssignmentValueSymbol(p);
        if (!v) return;
        t = ck.getTypeOfSymbolAtLocation(v, x);
      } else if (isDeclName(x)) return;
    } else if (!ts.isPropertyAccessExpression(x) && !ts.isElementAccessExpression(x)) return;
    let top: ts.Node = x;
    while (ts.isParenthesizedExpression(top.parent) || ts.isNonNullExpression(top.parent)) top = top.parent;
    const q = top.parent;
    if ((ts.isCallExpression(q) && q.expression === top) || (ts.isPropertyAccessExpression(q) && q.expression === top)) return;
    if (isFunctionValued(t ?? ck.getTypeAtLocation(x), env)) fail(x, `${who} may not use the function \`${nodeText(x, 40)}\` here other than by calling it (what it is passed to or stored in may call it); ${rule}`);
  };
  const visit = (x: ts.Node) => {
    if (ts.isTypeNode(x)) return; // (types: `xs.map<T>(…)`; a cast is reported at its expression)
    fnRef(x);
    if (ts.isNewExpression(x) || ts.isAwaitExpression(x) || ts.isDeleteExpression(x) || ts.isTaggedTemplateExpression(x)) fail(x, rule);
    // the code is not translated, so its static types are all that stands for what it can
    // reach: no cast (`(m as any).clear()`), no `arguments`, nothing typed `any`
    if ((ts.isAsExpression(x) && x.type.getText() !== "const") || ts.isTypeAssertionExpression(x)) fail(x, `type assertions are not allowed in VTS (they are unchecked casts); ${rule}`);
    if (ts.isIdentifier(x) && x.text === "arguments" && !(ts.isPropertyAccessExpression(x.parent) && x.parent.name === x)) fail(x, `\`arguments\` is not allowed in VTS; ${rule}`);
    if (ts.isBinaryExpression(x) && x.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && x.operatorToken.kind <= ts.SyntaxKind.LastAssignment) fail(x, rule);
    if ((ts.isPrefixUnaryExpression(x) || ts.isPostfixUnaryExpression(x)) && (x.operator === ts.SyntaxKind.PlusPlusToken || x.operator === ts.SyntaxKind.MinusMinusToken)) fail(x, rule);
    ts.forEachChild(x, visit);
    // (after the parts, so that a cast is reported as one)
    if (ts.isCallExpression(x)) call(x);
    if (ts.isExpression(x) && !(ts.isIdentifier(x) && ts.isPropertyAccessExpression(x.parent) && x.parent.name === x) && env.m.checker.getTypeAtLocation(x).flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) {
      fail(x, `\`${nodeText(x, 40)}\` has type any or unknown here, so VTS cannot tell what it does; ${rule}`);
    }
  };
  visit(n);
}

/* ───────────────────────────── JSX ───────────────────────────── */

function isJsx(e: ts.Node): boolean {
  return ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e) || ts.isJsxFragment(e);
}

/** How render blocks translate a JSX const at its declaration: a VNode of this render. */
function jsxConstCtx(comp: CompCtx): NonNullable<BlockCtx["jsxConst"]> {
  return {
    code: (e, env) => withBubble({ ...bubble, ns: "deferred", content: null }, () => jsxNode(e, env)),
    type: `VReact.VNode ${comp.stateType} E (${comp.invName} ${comp.propsVar}) ${comp.snap}`,
    key: (e) => translatedKey(stripParens(e)),
  };
}

/** A VNode term for a JSX-valued expression. */
export function jsxNode(e0: ts.Expression, env: Env): string {
  const e = ts.isParenthesizedExpression(e0) ? e0.expression : e0;
  if (ts.isParenthesizedExpression(e)) return jsxNode(e.expression, env);
  if (e.kind === ts.SyntaxKind.NullKeyword || isGlobal(env, e, "undefined") || e.kind === ts.SyntaxKind.FalseKeyword) return "VReact.VNode.empty";
  if (ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) return element(e, env);
  if (ts.isJsxFragment(e)) return `(VReact.VNode.elem "fragment" [] [] ${children(e.children, env, e, "<>…</>")})`;
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
    case "map":
    case "set":
      fail(e, `a ${v.type.k === "map" ? "Map" : "Set"} is not a valid React child (React renders it as a list of its ${v.type.k === "map" ? "entries" : "elements"}, without keys, and warns): render a keyed list, e.g. {[...${nodeText(e, 20)}.values()].map((x) => <li key={…}>…</li>)}`);
    default:
      fail(e, `cannot render a value of type ${showType(v.type)} (arrays need .map with keys)`);
  }
}

/**
 * The children of an element or a fragment (`parent`, described as `what`).  React reconciles
 * them as one array, so the explicit keys of the elements in it must be pairwise distinct
 * (`siblingKeys`).
 */
function children(cs: ts.NodeArray<ts.JsxChild>, env: Env, parent: ts.Node, what: string): string {
  const items: string[] = [];
  const slots: Slot[] = [];
  const child = (x: ts.Expression) => {
    const from = env.m.mark();
    items.push(jsxNode(x, env));
    const el = parensOnly(x);
    // (the key of an element child, as just translated in it)
    slots.push({ expr: x, from, to: env.m.mark(), key: ts.isJsxElement(el) || ts.isJsxSelfClosingElement(el) ? translatedKey(el) : undefined });
  };
  for (const c of cs) {
    if (ts.isJsxText(c)) {
      const t = jsxTextValue(c.text, c);
      if (t) items.push(`(VReact.VNode.text ${jsStr(t)})`);
      continue;
    }
    if (ts.isJsxExpression(c)) {
      if (!c.expression) continue;
      if (c.dotDotDotToken) fail(c, "spread children are not supported");
      child(c.expression);
      continue;
    }
    child(c as ts.Expression);
  }
  const list = items.length ? `(VReact.VList.ofList [\n    ${items.map((i) => indent(i, 2).trimStart()).join(",\n    ")}])` : "VReact.VList.nil";
  return siblingKeys(slots, env, parent, what, list);
}

/**
 * A child of an element or fragment written as an expression or an element: its translation
 * ran between the marks `from` and `to` (to translate it again for its keys, `ModCtx.replay`);
 * `key` is the translated `key={…}` of an element child.
 */
interface Slot {
  expr: ts.Expression;
  from: Mark;
  to: Mark;
  key: Val | undefined;
}

/** `e` without parentheses (what `jsxNode` looks through). */
function parensOnly(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  return e;
}

/** An explicitly keyed element that a child can put into its parent's children array. */
interface SiblingKey {
  attr: ts.JsxAttribute;
  /** the key, when it is written as a string (`key="a"`, `key={"a"}`) */
  lit: string | null;
  /** the child is this element, unconditionally */
  always: boolean;
}

/** The `key` attribute of a JSX element, or null. */
function keyAttrOf(e: ts.JsxElement | ts.JsxSelfClosingElement): ts.JsxAttribute | null {
  for (const a of attrs(e)) if (ts.isJsxAttribute(a) && a.name.getText() === "key") return a;
  return null;
}

/** The JSX const a child expression names (`{row}`), or null. */
function jsxConstOf(e: ts.Expression, env: Env): { node: ts.Expression; env: Env; key: Val | undefined } | null {
  if (!ts.isIdentifier(e)) return null;
  const s = symbolOf(env, e);
  const b = s ? env.vars.get(s) : undefined;
  return b?.k === "jsx" ? { node: b.node, env: b.env, key: b.key } : null;
}

/**
 * The explicitly keyed elements that the child `e0` can put at the top level of the children
 * array it is in, following `jsxNode`: the element itself, the branches of `c ? a : b` and
 * `c && a`, the element of a JSX const.  A fragment and a keyed list (`xs.map(…)`) are one child
 * of the array (React makes each a fragment fiber), whose keys are those of an array of its own.
 */
function siblingKeysOf(e0: ts.Expression, env: Env, always: boolean, out: SiblingKey[]): SiblingKey[] {
  const e = stripParens(e0);
  if (ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) {
    const a = keyedByMap.has(e) ? null : keyAttrOf(e);
    if (a) out.push({ attr: a, lit: literalAttr(a), always });
  } else if (ts.isConditionalExpression(e)) {
    siblingKeysOf(e.whenTrue, env, false, out);
    siblingKeysOf(e.whenFalse, env, false, out);
  } else if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) {
    siblingKeysOf(e.right, env, false, out);
  } else {
    const c = jsxConstOf(e, env);
    if (c) siblingKeysOf(c.node, c.env, always, out);
  }
  return out;
}

/**
 * React 18 compares the keys of the elements of one children array as strings (`'' + key`:
 * `key={1}` and `key="1"` are the same key) and requires them to be pairwise distinct: with two
 * equal keys, `reconcileChildrenArray` warns ("Encountered two children with the same key") and,
 * once an update leaves its first pass, `mapRemainingChildren` keeps one old fiber per key, so the
 * other is neither reused nor deleted — its DOM stays, with stale handlers, and it is never
 * unmounted.  The model reconciles these children by position (`VNode.withKey`), which matches
 * React only when the keys are distinct.  So when two or more children of `parent` may have an
 * explicit key, two that are always present with the same written key are rejected, and unless
 * all keys are strings that differ between children, the children carry a `unique-keys`
 * obligation (`VList.withKeys`) over the keys of the children present, as strings.
 */
function siblingKeys(slots: Slot[], env: Env, parent: ts.Node, what: string, list: string): string {
  const keyed = slots.map((s) => ({ slot: s, keys: siblingKeysOf(s.expr, env, true, []) })).filter((s) => s.keys.length);
  if (keyed.length < 2) return list;
  const seen = new Map<string, SiblingKey>();
  for (const { keys } of keyed) {
    for (const k of keys) {
      if (!k.always || k.lit === null) continue;
      if (seen.has(k.lit)) fail(k.attr, `two children of ${what} have the same key ${JSON.stringify(k.lit)}: React requires the keys of the children of one element to be distinct (with two equal keys it can duplicate or omit children, and one of them stays mounted, with its handlers, after it is removed); give them distinct keys`);
      seen.set(k.lit, k);
    }
  }
  // keys written as strings that no two children share: distinct, whichever are present
  const lits = keyed.map(({ keys }) => keys.map((k) => k.lit));
  if (lits.every((ls) => ls.every((l) => l !== null)) && lits.every((ls, i) => ls.every((l) => lits.every((other, j) => j === i || !other.includes(l))))) return list;
  const parts = keyed.map(({ slot }) => slotKeysTerm(slot, env));
  const shown = keyed.flatMap(({ keys }) => keys.map((k) => (k.lit !== null ? JSON.stringify(k.lit) : nodeText(attrValue(k.attr)!, 40))));
  const ob = env.m.ob(parent, "unique-keys", `the keys of the children of ${what} are distinct (React compares them as strings): ${shown.join(", ")}`);
  return `(VReact.VList.withKeys (${parts.join(" ++\n    ")})\n  ${ob}\n  ${list})`;
}

/**
 * The keys (as strings, in a Lean list) that the child `s` puts into its parent's children
 * array.  Each key is the term already translated for the element (`key={…}` in `VNode.withKey`),
 * with the same obligations: the copies are the same obligations, so a failing one is reported
 * once.  An element child: its key as translated in it.  A JSX const: its key as translated at its
 * declaration, where JS evaluates it (the Lean local names there are still in scope: later locals
 * get fresh names).  A conditional child: its translation is replayed (`ModCtx.replay`: the same
 * text, conditions, hypothesis names and obligation ids), building the same conditionals over the
 * keys of the branches.
 */
function slotKeysTerm(s: Slot, env: Env): string {
  const e = parensOnly(s.expr);
  if (ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) return elementKeysTerm(e, s.key, env);
  const c = jsxConstOf(e, env);
  if (c) return elementKeysTerm(c.node, c.key, env);
  return env.m.replay(s.from, s.to, () => replayKeys(s.expr, env));
}

/** The translation of `jsxNode(e0, env)` again (the same calls, in order), returning the keys `e0` puts into the array. */
function replayKeys(e0: ts.Expression, env: Env): string {
  const e = ts.isParenthesizedExpression(e0) ? e0.expression : e0;
  if (ts.isParenthesizedExpression(e)) return replayKeys(e.expression, env);
  if (ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) {
    element(e, env);
    return elementKeysTerm(e, translatedKey(e), env);
  }
  if (ts.isConditionalExpression(e)) return branch(e.condition, env, (e1) => replayKeys(e.whenTrue, e1), (e2) => replayKeys(e.whenFalse, e2));
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) {
    return branch(e.left, env, (e1) => replayKeys(e.right, e1), () => "[]");
  }
  jsxNode(e, env);
  const c = jsxConstOf(e, env);
  return c ? elementKeysTerm(c.node, c.key, env) : "[]";
}

/** The keys an element (or a JSX const's node) puts into the array: its `key` (`v`: as translated), or none. */
function elementKeysTerm(e: ts.Expression, v: Val | undefined, env: Env): string {
  if (!(ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e)) || keyedByMap.has(e)) return "[]";
  const a = keyAttrOf(e);
  return a ? keyString(a, v, env) : "[]";
}

/**
 * The key of `key={…}` as React sees it, `'' + key`, as a Lean list: one string, or none for
 * `undefined` (React's `jsx()` ignores an undefined key, but makes a null one the key "null").
 * `v` is the key's translation (none for a key written as a string).
 */
function keyString(a: ts.JsxAttribute, v: Val | undefined, env: Env): string {
  const lit = literalAttr(a);
  if (lit !== null) return `[${jsStr(lit)}]`;
  const val = attrValue(a)!;
  if (!v) throw new Error(`internal error: the key ${nodeText(val, 40)} was not translated where its element was`);
  const scalar = (t: VType) => ["str", "int", "num", "bool", "enum"].includes(t.k);
  if (scalar(v.type)) return `[${toStr(v, val, env)}]`;
  if (v.type.k === "opt" && scalar(v.type.elem)) {
    const kinds = nullishKinds(val, env);
    // (the arm uses only its binder, so a fixed name cannot capture; no fresh name: a replay must
    // not count hypotheses the translation it repeats did not)
    const x = "key₀";
    return `(match ${v.code} with | some ${x} => [${toStr({ code: x, type: v.type.elem }, val, env)}] | none => [${!kinds || kinds.null ? jsStr("null") : ""}])`;
  }
  fail(val, `a key of type ${showType(v.type)} next to other keyed children: React compares the keys of the children of one element as strings ('' + key), which VTS models for string, int, number, boolean and string-enum keys (and their optional forms); key by one of these`);
}

function attrs(e: ts.JsxElement | ts.JsxSelfClosingElement): ts.NodeArray<ts.JsxAttributeLike> {
  return ts.isJsxElement(e) ? e.openingElement.attributes.properties : e.attributes.properties;
}

/**
 * The element a JSX tag creates, as the JSX transform decides (TypeScript's
 * `isIntrinsicJsxName`, Babel's `isCompatTag`): a plain name starting with a lower-case
 * letter is the HTML element of that name — never a variable of that name —, a capitalised
 * name is the value of that identifier (a component).  Any other tag is rejected: a member
 * expression `<props.as>` / `<ui.Button>` is the value it evaluates to (a dynamic element
 * type: whatever tag name or component it holds), a namespaced `<a:b>` is an XML name, and
 * a name with a dash `<my-el>` is a custom element, whose behaviour (events, activation,
 * form association) is defined by script outside the program.
 */
function element(e: ts.JsxElement | ts.JsxSelfClosingElement, env: Env): string {
  const tagNode = ts.isJsxElement(e) ? e.openingElement.tagName : e.tagName;
  const tag = tagNode.getText();
  const kids = ts.isJsxElement(e) ? e.children : undefined;
  if (ts.isJsxNamespacedName(tagNode)) fail(tagNode, `namespaced JSX tags (<${tag}>) are not supported: use an HTML element (<div>, <button>, …) or a verified component`);
  // (`<L.Row>`, L a verified module's namespace, is not dynamic, but VTS reads a component tag only as a name)
  const nm = ts.isPropertyAccessExpression(tagNode) ? nsMember(env, tagNode) : null;
  if (nm && ts.isPropertyAccessExpression(tagNode)) {
    const x = tagNode.name.text;
    fail(tagNode, `<${tag}> names ${nm.g?.k === "comp" ? "the component " : ""}\`${x}\` through the module namespace \`${tagNode.expression.getText()}\`: VTS reads a component tag only as a plain name; import it by name (\`import { ${x} } from …\`) and write <${x} …/>`);
  }
  if (!ts.isIdentifier(tagNode)) fail(tagNode, `<${tag}> is a dynamic element type: JSX renders whatever \`${tag}\` holds (an HTML tag name or a component), which VTS does not model. Write the element (<button>) or the component (<Row>, imported by name) directly, e.g. under a condition`);
  if (tagNode.text !== tag) fail(tagNode, `<${tag}>: write the tag name without escapes`);
  if (tag.includes("-")) fail(tagNode, `<${tag}> is a custom element: its behaviour (events, activation, form submission) is defined by script outside the verified program; use HTML elements and verified components`);
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
 * Which element a click activates is not the DOM-spec rule (the innermost element
 * with an activation behaviour) in Chromium: there the default handling of a click
 * dispatches `DOMActivate` at its target, which bubbles to an enclosing `<button>`
 * and submits, resets or invokes it, unless the target handles the click itself —
 * only a checkbox, a radio button and a link do (`stopsButtonActivation`).  So a
 * click on a nested button, a text field, a `<summary>`, a `<label>` (twice: once
 * for the click, once for the click it dispatches to its control) or the content of
 * a link inside a submit button submits.  A label is stopped by interactive content
 * and everything in it (`stopsLabelActivation`).
 *
 * Implicit submission by Enter and the keyboard activation of buttons follow
 * trusted key events only, which the browser dispatches from native code, with
 * microtask checkpoints in between.  The model runs one handler per event, so VTS
 * rejects every layout in which one discrete event, with its activation behaviour,
 * could run two discrete handlers, or one twice: two handler props of one element
 * sharing a native event; an element with handlers containing a descendant handler
 * that shares a native event, or a user component; `onClick` on, around, or within
 * (except on a checkbox, radio button or link) a submit/reset button whose form owner
 * has `onSubmit`/`onReset` at or above it — or that names its form (`form=…`), which
 * may be anywhere —, or an invoker button; `onClick` on, around, or within (not
 * inside interactive content) a `<label>`; a label, or another such button, within
 * such a button; a user component within such a button or a label.
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
  /** the namespace React creates the elements at this position in (`Namespace`) */
  ns: Namespace;
  /** directly inside a `<select>`, `<optgroup>` or `<option>`: that tag, whose content is restricted (`CONTENT_RULES`); null: any content */
  content: string | null;
  /** the nearest enclosing focus handler (focusin/focusout) that updates state (`onBlur on <div>`): no autoFocus element may be inside it (`focusesOnMount`), unless its component never mounts one again (`autoFocusRemount`) */
  focusUpd: string | null;
}
interface Activation {
  /** `a <label>`, `a submit button <button> of a form with onSubmit on <form>` */
  what: string;
  label: boolean;
}
/**
 * The namespace of an element, as react-dom 18.3.1 decides (`getIntrinsicNamespace`,
 * `getChildNamespace`): below an HTML element, `<svg>` is an SVG element and `<math>` a MathML
 * element, anything else HTML; below an SVG or MathML element, every element is in that
 * namespace — an `<input>` inside `<svg>` is an SVG element named input, with no value, type
 * or activation behaviour — except the children of an SVG `<foreignObject>`, which are HTML.
 * A component's root is HTML (VTS rejects user components in another namespace).
 * `deferred`: the JSX of a JSX const where it is declared, whose namespace is that of the
 * position where it is rendered, checked there (`jsxNode` translates it again at each use);
 * the declaration is translated as HTML without the namespace's rejections.
 */
type Namespace = "html" | "svg" | "math" | "deferred";
const NO_BUBBLE: Bubble = { natives: new Map(), handlers: [], onClick: null, form: null, act: null, ns: "html", content: null, focusUpd: null };

/**
 * The content of a `<select>`, an `<optgroup>` and an `<option>` (HTML elements): the elements
 * each may contain, besides text — react-dom 18.3.1's `validateDOMNesting`
 * (`isTagValidWithParent`): a select holds `<option>`s and `<optgroup>`s, an optgroup
 * `<option>`s, an option text only.  React only warns about other content and creates it with
 * the DOM API, where it is a real event target; but VTS's event model relies on these rules.
 * react-dom's ChangeEventPlugin picks the native events that make an `onChange` by the
 * *target* control and collects `onChange` on the whole path from it to the root: a checkbox
 * inside a select would run the select's `onChange` on a click, a text field on an `input`,
 * with that control as `e.target`.  With this content, a select's `onChange` runs on the
 * select's own `change` event only (`changeNatives`; an option or optgroup never makes an
 * `onChange`), with the select as `e.target` (a text node is never React's target:
 * `getEventTarget` takes its parent).  No user component either: its elements are checked as a
 * tree of their own.
 */
const CONTENT_RULES: ReadonlyMap<string, readonly string[]> = new Map([
  ["select", ["option", "optgroup"]],
  ["optgroup", ["option"]],
  ["option", []],
]);

/** Rejects `what` (an element, or a user component) directly inside `<parent>`, whose content `CONTENT_RULES` restricts. */
function failContent(at: ts.Node, what: string, parent: string, component: boolean): never {
  const allowed = CONTENT_RULES.get(parent)!;
  const may = allowed.length ? `${allowed.map((t) => `<${t}>`).join(" and ")} elements${component ? " written in this component" : ""} and text` : "text (its label)";
  fail(at, `${what} inside <${parent}>: ${parent === "select" ? "a" : "an"} <${parent}> may contain only ${may}, as react-dom's validateDOMNesting says (React only warns, and creates it anyway). VTS models a <select>'s onChange as run by the select's own change event, with the select as e.target, but react-dom also runs it for a click on a checkbox or an input in a text field anywhere inside the select, with that element as e.target; ${parent === "option" ? "write the option's label as text (a string or a number, also in {…})" : `put ${component ? "the component" : "the element"} next to the <select>`}`);
}
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

/**
 * `<button>` / `<input>`: may a click on it submit / reset its form owner?  A dynamic `type` may
 * do either.  An SVG or MathML element (`html` false) named so is not a form control.
 */
function formActivation(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, html: boolean): { submit: boolean; reset: boolean } {
  if (!html || (tag !== "button" && tag !== "input")) return { submit: false, reset: false };
  const t = staticAttr(e, "type");
  if (t === undefined) return { submit: true, reset: true };
  if (tag === "button") {
    const ty = asciiLower(t ?? ""); // missing or invalid: the submit button state
    return { submit: ty !== "button" && ty !== "reset", reset: ty === "reset" };
  }
  const ty = asciiLower(t ?? "text");
  return { submit: ty === "submit" || ty === "image", reset: ty === "reset" };
}

/**
 * Is `<tag>` interactive content, so that a click on it, or on anything inside it,
 * does not activate an enclosing `<label>`?  (HTML "interactive content"; Chromium's
 * `IsInInteractiveContent`, which walks from the click's target up to the label.)
 * A `<summary>` is not: outside a `<details>` it is plain content to Chromium, and a
 * details' own summary lies inside the `<details>`, which is.  Unsure cases (a dynamic
 * `type` or `href`) do not stop the label, nor does an SVG or MathML element (`html` false: not
 * HTML interactive content, also an SVG `<a href>`).
 */
function stopsLabelActivation(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, html: boolean): boolean {
  if (!html) return false;
  if (["button", "label", "select", "textarea", "details"].includes(tag)) return true;
  if (tag === "a") return typeof staticAttr(e, "href") === "string";
  if (tag === "input") {
    const t = staticAttr(e, "type");
    return t !== undefined && asciiLower(t ?? "text") !== "hidden";
  }
  return false;
}

/**
 * Does a click whose target is `<tag>` itself not activate an enclosing submit,
 * reset or command button?  Not the DOM-spec rule ("the click's activation target is
 * the innermost element with an activation behaviour"), which jsdom follows, but
 * Chromium's: the default handling of a click dispatches `DOMActivate` at its target
 * — which bubbles to the enclosing `<button>` and submits, resets or invokes it —
 * unless the target's own default handler marks the click handled.  Only a checkbox
 * or radio button (its click toggles it) and a link (`<a href>`: it navigates) do;
 * a nested `<button>`, `<input type=button|file|color|text>`, `<select>`,
 * `<textarea>`, `<summary>`, `<details>`, `<img>` and the content of a link do not
 * (Chromium 152, react-dom 18.3.1).  It covers this element only, never its
 * descendants: a click on a span inside a link inside the button submits.  Unsure
 * cases (a dynamic `type` or `href`) do not stop the button, nor does an SVG or MathML element
 * (`html` false: an `<input type="checkbox">` inside `<svg>` is no checkbox).
 */
function stopsButtonActivation(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, html: boolean): boolean {
  if (!html) return false;
  if (tag === "a") return typeof staticAttr(e, "href") === "string";
  if (tag === "input") {
    const t = staticAttr(e, "type");
    return typeof t === "string" && ["checkbox", "radio"].includes(asciiLower(t));
  }
  return false;
}

/**
 * Check the handler props of `<tag>` against each other and the enclosing elements; returns the
 * context for its children.  `ns`: the element's namespace; `childNs`: its children's.
 */
function checkEvents(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, handlers: ts.JsxAttribute[], infos: Map<ts.JsxAttribute, EventInfo>, ns: Namespace, childNs: Namespace): Bubble {
  const html = ns === "html" || ns === "deferred";
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
  // activation: the enclosing activator a click on this element still activates
  // (`enclosing`), the one a click inside it does (`passOn`, for the children), and
  // this element's own (`mine`).  Interactive content stops a label for itself and
  // its content; a checkbox, radio or link stops a button for itself only.
  let enclosing = bubble.act;
  let passOn = bubble.act;
  if (bubble.act?.label && stopsLabelActivation(tag, e, html)) enclosing = passOn = null;
  else if (bubble.act && !bubble.act.label && stopsButtonActivation(tag, e, html)) enclosing = null;
  let mine: Activation | null = null;
  const fa = formActivation(tag, e, html);
  if (html && tag === "label") {
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
  if (!mine && html && tag === "button" && (attrsNamed(e, "commandfor").length || attrsNamed(e, "command").length)) {
    mine = { what: "a command button <button> (commandfor/command: the element it controls, anywhere, may run a handler — request-close fires cancel at a dialog)", label: false };
    if (onClick) fail(e, `onClick on ${mine.what}: one click runs both handlers, ${SCRIPTED} (put the logic in the target's handler)`);
    if (bubble.onClick) fail(e, `${mine.what} is nested inside an element with ${bubble.onClick}: one click runs both handlers, ${SCRIPTED} (move the handler)`);
  }
  // an activator inside one that a click on it still activates (only a button can
  // enclose one: interactive content stops a label): in Chromium one click activates
  // both — a label inside a submit button submits its form twice (once for the click,
  // once for the click it dispatches to its control), a nested command button runs
  // its command and the enclosing button submits
  if (mine && enclosing) fail(e, `${mine.what} inside ${enclosing.what}: one click on it, or inside it, activates both (in Chromium the default handling of the click bubbles to the enclosing button), so one click runs two handlers, or one twice, ${SCRIPTED} (do not nest it in the button)`);
  if (enclosing && onClick) fail(e, `onClick on <${tag}> inside ${enclosing.what}: one click runs this handler and, through the activation of the enclosing element, another one (or this one again), ${SCRIPTED} (move the handler out${enclosing.label ? "" : "; inside a button, only a checkbox, a radio button or an <a href> handles its own click"})`);
  const natives = new Map(bubble.natives);
  for (const [n, p] of own) natives.set(n, `${p} on <${tag}>`);
  const handlerOf = (prop: string) => (names.includes(prop) ? `${prop} on <${tag}>` : null);
  return {
    natives,
    handlers: [...bubble.handlers, ...names],
    onClick: onClick ? `onClick on <${tag}>` : bubble.onClick,
    form: html && tag === "form" ? { submit: handlerOf("onSubmit") ?? bubble.natives.get("submit") ?? null, reset: handlerOf("onReset") ?? bubble.natives.get("reset") ?? null } : bubble.form,
    act: mine ?? passOn,
    ns: childNs,
    content: html && CONTENT_RULES.has(tag) ? tag : null,
    focusUpd: bubble.focusUpd,
  };
}

/**
 * React 18.3.1's `voidElementTags`: `assertValidProps` throws while rendering one of these
 * (whatever its namespace: React decides by the tag name) when it has children, also given as
 * a `children` attribute.
 */
const VOID_TAGS = new Set(["area", "base", "br", "col", "embed", "hr", "img", "input", "keygen", "link", "meta", "param", "source", "track", "wbr", "menuitem"]);

/**
 * Tags that react-dom (its input/select/textarea/option wrappers, by tag name) or VTS's event
 * and activation checks treat as HTML form controls, labels, forms and the like.  Inside `<svg>`
 * or `<math>` such an element is an SVG (MathML) element of that name, with none of that
 * behaviour (and React's wrappers misbehave on it: a `<select value>` there throws on mount).
 */
const HTML_ONLY_TAGS = new Set(["input", "select", "textarea", "option", "optgroup", "button", "label", "form", "fieldset", "output", "data", "details", "summary", "dialog", "datalist", "meter", "progress"]);

/** The children JSX passes to an element: not whitespace that JSX drops, nor `{}` / `{/* comment *\/}`. */
function passedChildren(kids: ts.NodeArray<ts.JsxChild> | undefined): ts.JsxChild[] {
  return (kids ?? []).filter((c) => !(ts.isJsxText(c) && !jsxTextValue(c.text, c)) && !(ts.isJsxExpression(c) && !c.expression));
}

/**
 * The namespace of the element `<tag>` at the current position, and that of its children (see
 * `Namespace`); rejects tag names the document would read otherwise than VTS's checks.
 */
function namespaces(tag: string, tagNode: ts.Node): { ns: Namespace; childNs: Namespace } {
  const ns: Namespace = bubble.ns === "html" || bubble.ns === "deferred" ? (tag === "svg" ? "svg" : tag === "math" ? "math" : bubble.ns) : bubble.ns;
  // React creates an SVG <script> with createElementNS, and it runs when React inserts it (an
  // HTML one, created through innerHTML, never runs): either way, script outside the program
  if (tag === "script") fail(tagNode, `<script> is not supported: its code is outside the verified program (inside <svg> React inserts a script that runs)`);
  if (ns === "html") {
    // document.createElement lower-cases the name in an HTML document: <bUTTON> is a <button>
    if (/[A-Z]/.test(tag) && /^[A-Za-z][A-Za-z0-9]*$/.test(tag)) fail(tagNode, `<${tag}>: outside <svg> and <math> this is an HTML element, and an HTML document lower-cases element names, so it is a <${asciiLower(tag)}> (with that element's behaviour); write <${asciiLower(tag)}>, or put an SVG element inside <svg>`);
    if (!/^[a-z][a-z0-9]*$/.test(tag)) fail(tagNode, `<${tag}> is not an HTML element name (letters a-z and digits)`);
  } else if (ns !== "deferred") {
    if (!/^[a-z][A-Za-z0-9]*$/.test(tag)) fail(tagNode, `<${tag}> is not an ${ns === "svg" ? "SVG" : "MathML"} element name (ASCII letters and digits)`);
    if (HTML_ONLY_TAGS.has(tag)) {
      fail(tagNode, `<${tag}> inside <${ns}> is an ${ns === "svg" ? "SVG" : "MathML"} element named ${tag}, not an HTML one: React creates the elements inside <${ns}>${ns === "svg" ? " (except inside <foreignObject>)" : ""} in the ${ns === "svg" ? "SVG" : "MathML"} namespace, where it has no value, type, form or activation behaviour; put it outside the <${ns}>${ns === "svg" ? ", or inside a <foreignObject>" : ""}`);
    }
  }
  return { ns, childNs: ns === "svg" && tag === "foreignObject" ? "html" : ns };
}

/**
 * Why a focus handler that updates state may not run in the commit that mounts an autoFocus
 * element: react-dom 18.3.1 focuses an autoFocus `<button>`, `<input>`, `<select>` or `<textarea>`
 * in the commit that mounts it (`commitMount`, with React's event system enabled again), so the
 * focusout and focusin events run onBlur on the element that had focus and onFocus on the
 * autoFocus element and the elements around them, synchronously. Their updates are discrete
 * (SyncLane) and React renders and commits them at once, at the end of that commit; if that
 * commit mounts an autoFocus element again (one whose key or presence depends on the state), the
 * chain goes on, and after 50 nested commits the setter throws "Maximum update depth exceeded"
 * (`checkForNestedUpdates`) — inside the handler. With no updates in the focus handlers of an
 * autoFocus element and of the elements around one, only the element that had focus before the
 * first such commit can update state (once: it does not get focus back inside the chain), so the
 * chain stops after one more commit. (A component inside an element with handlers is rejected, so
 * the elements around an autoFocus element that have handlers are in its component.)
 *
 * Such updates are accepted in a component no render of which mounts an autoFocus element after
 * its first (`autoFocusRemount` is null): a focus handler is robust, so it updates only its own
 * component's state (no parent callbacks), and React renders and commits that component's
 * subtree only, which then mounts no autoFocus element and focuses nothing (VTS has no layout
 * effects, and the passive effects React runs at the end of such a commit have default-priority
 * updates, which are rendered later); so inside a chain these updates add one commit that starts
 * no further one, and the argument above still bounds the chain.
 */
const AUTOFOCUS_CHAIN = "React focuses an autoFocus element in the commit that mounts it, which runs the focus handlers (onFocus, onBlur) of it, of the element that loses focus and of the elements around them synchronously inside that commit; their updates are rendered and committed at once, and when that commit mounts an autoFocus element again (its key or presence depends on the state), the chain repeats until React throws \"Maximum update depth exceeded\" from the setter, after 50 nested commits";

/** React 18.3.1 focuses these elements in the commit that mounts them when their `autoFocus` prop is truthy (`commitMount`). */
const AUTOFOCUS_TAGS = new Set(["button", "input", "select", "textarea"]);

/** The `autoFocus` attribute of `<tag>` when React may focus it as it mounts it (any letter case, any value but a literal false); null otherwise. */
function focusesOnMount(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, html: boolean): ts.JsxAttribute | null {
  if (!html || !AUTOFOCUS_TAGS.has(tag)) return null;
  return attrsNamed(e, "autofocus").find((a) => {
    const v = a.initializer && ts.isJsxExpression(a.initializer) ? a.initializer.expression : undefined;
    return !(v && stripParens(v).kind === ts.SyntaxKind.FalseKeyword);
  }) ?? null;
}

const autoFocusRemounts = new WeakMap<ts.FunctionDeclaration, { why: string | null }>();

/**
 * Why a render of the component `decl` after its first may mount an autoFocus element (null when
 * none does): it renders another component (which may have autoFocus elements under a condition
 * of its props), or one of its own autoFocus elements is not created by its first render and kept
 * by every later one (`notKept`). Only the component's own JSX matters besides: JSX occurs only in
 * the value a component returns (with the local JSX constants and list callbacks of that value),
 * and ReactNode props are rejected.
 */
function autoFocusRemount(decl: ts.FunctionDeclaration): string | null {
  const hit = autoFocusRemounts.get(decl);
  if (hit) return hit.why;
  let why: string | null = null;
  const body = decl.body;
  /** the component's returns (not those of nested functions) */
  const returns: ts.ReturnStatement[] = [];
  const findReturns = (n: ts.Node) => {
    if (ts.isReturnStatement(n)) returns.push(n);
    if (!ts.isFunctionLike(n) && !ts.isClassLike(n)) ts.forEachChild(n, findReturns);
  };
  body?.statements.forEach(findReturns);
  const only = returns.length === 1 && returns[0].parent === body ? returns[0] : null;
  const name = decl.name?.text ?? "the component";
  const line = (n: ts.Node) => n.getSourceFile().getLineAndCharacterOfPosition(n.getStart()).line + 1;
  const visit = (n: ts.Node) => {
    if (why) return;
    if (ts.isJsxSelfClosingElement(n) || ts.isJsxOpeningElement(n)) {
      const tag = n.tagName.getText();
      const el = ts.isJsxOpeningElement(n) ? n.parent : n;
      if (!ts.isIdentifier(n.tagName) || !/^[a-z]/.test(tag)) why = `${name} renders <${tag}> (line ${line(n)}), whose own autoFocus elements a render may mount`;
      else if (focusesOnMount(tag, el, true)) {
        const r = notKept(el, only, returns.length);
        if (r) why = `its <${tag} autoFocus> on line ${line(n)} ${r}`;
      }
    }
    ts.forEachChild(n, visit);
  };
  if (body) visit(body);
  autoFocusRemounts.set(decl, { why });
  return why;
}

/**
 * Why the element `el` is not created by the first render of its component and kept by every
 * later one (null when it is): it must be written in the component's only return (`ret`, a
 * statement of the body itself), reached from the returned value through elements and fragments
 * only — not under a condition, in a list or a local constant — with no `key` on it or on an
 * element around it. (React matches the children of an element by key, or by index when they have
 * none; a `{…}` child, whatever it renders, keeps the index of the children after it.)
 */
function notKept(el: ts.JsxElement | ts.JsxSelfClosingElement, ret: ts.ReturnStatement | null, returns: number): string | null {
  let n: ts.Node = el;
  for (;;) {
    if ((ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n)) && attrsNamed(n, "key").length) return n === el ? "has a key" : "is inside an element with a key";
    const p: ts.Node = n.parent;
    if (ts.isJsxElement(p) && p.children.some((c) => c === n)) {
      n = p;
      continue;
    }
    if (ts.isJsxFragment(p) || ts.isParenthesizedExpression(p)) {
      n = p;
      continue;
    }
    if (ts.isReturnStatement(p)) return p === ret ? null : returns > 1 ? "is in one of several returns" : "is not in the component's own return";
    return "is rendered under a condition, in a list or through a local constant";
  }
}

function intrinsic(tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  const comp = env.comp!;
  const tagNode = ts.isJsxElement(e) ? e.openingElement.tagName : e.tagName;
  const { ns, childNs } = namespaces(tag, tagNode);
  if (bubble.content !== null && !CONTENT_RULES.get(bubble.content)!.includes(tag)) failContent(tagNode, `<${tag}>`, bubble.content, false);
  const html = ns === "html" || ns === "deferred";
  const handlerAttrs = attrs(e).filter(ts.isJsxAttribute).filter((a) => /^on[A-Z]/.test(a.name.getText()));
  const infos = new Map(handlerAttrs.map((a) => [a, eventInfo(a.name.getText(), tag, e, a, html)] as const));
  let inner = checkEvents(tag, e, handlerAttrs, infos, ns, childNs);
  const autoFocus = focusesOnMount(tag, e, html);
  /** why a later render of this component may mount an autoFocus element (AUTOFOCUS_CHAIN), or null */
  const remount = () => autoFocusRemount(comp.info.decl);
  const keep = `, or keep every autoFocus element of ${comp.info.name} mounted from its first render on: written in its only return, not under a condition or in a list, with no key on it or around it, in a component that renders no other component`;
  if (autoFocus && bubble.focusUpd) {
    const why = remount();
    if (why) fail(autoFocus, `autoFocus on <${tag}> inside an element with ${bubble.focusUpd}, which updates state, and a later render of ${comp.info.name} may mount an autoFocus element (${why}): ${AUTOFOCUS_CHAIN} (move that handler to an element that does not contain this one, or drop autoFocus${keep})`);
  }
  /** focus handlers of this element that update state (on an autoFocus element only in a component that never mounts one again: `autoFocusRemount`) */
  const focusUpd: string[] = [];
  // react-dom throws while rendering a void element with children, and a <textarea> with
  // children and a defaultValue (or several children); a textarea's children are its value
  const passed = passedChildren(kids);
  if (VOID_TAGS.has(tag) && passed.length) fail(passed[0], `<${tag}> is a void element: React throws while rendering it with children ("${tag} is a void element tag and must neither have \`children\` …"); put the content next to it`);
  if (tag === "textarea" && passed.length) fail(passed[0], `children of a <textarea> are its initial value to React, not elements (React throws when it also has a defaultValue, or more than one child): use value={…} with onChange, or defaultValue={…}`);
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
    if (RESERVED_PROPS.includes(name)) fail(a, `${name} is not an attribute: ${RESERVED_WHY(name)}`);
    checkAttribute(a, asciiLower(name), tag, e, env);
    const val = attrValue(a);
    if (/^on[A-Z]/.test(name)) {
      if (!val) fail(a, "handler attribute needs a value");
      const info = infos.get(a)!;
      const ev = info.model;
      // a focus handler (focusin/focusout) of an autoFocus element, or of an element around one,
      // runs inside the commit that mounts the autoFocus element (AUTOFOCUS_CHAIN)
      const focusSide = info.natives.some((n) => n === "focusin" || n === "focusout");
      const probe = { updated: false };
      const why = focusSide && autoFocus ? remount() : null;
      const noUpdates = why ? `${name} on <${tag}> with autoFocus updates state, and a later render of ${comp.info.name} may mount an autoFocus element (${why}): ${AUTOFOCUS_CHAIN} (drop autoFocus, or the update${keep})` : undefined;
      const h = handlerFn(val, env, info.discrete ? "discrete" : "robust", { tag, prop: name, html, ...(focusSide ? { probe, noUpdates } : {}) });
      if (probe.updated) focusUpd.push(`${name} on <${tag}>`);
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
      as.push(`⟨${leanStr(name)}, VReact.AttrVal.str ${jsStr(jsxAttrText(val))}⟩`);
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
  if (focusUpd.length) inner = { ...inner, focusUpd: focusUpd[0] };
  const ch = kids ? withBubble(inner, () => children(kids, env, e, `<${tag}>`)) : "VReact.VList.nil";
  return withKey(key, `(VReact.VNode.elem ${leanStr(tag)} [${as.join(", ")}]\n  [${hs.join(",\n   ")}]\n  ${ch})`);
}

/** Attributes whose value is a URL the browser may navigate to or load as a document (ASCII-lower-cased names). */
const URL_ATTRS = new Set(["href", "xlink:href", "xlinkhref", "src", "action", "formaction", "data"]);

/** The value of a JSX attribute given as a string (`"x"`, decoded, or `{"x"}`); null otherwise. */
function literalAttr(a: ts.JsxAttribute): string | null {
  const v = attrValue(a);
  if (!v) return null;
  if (ts.isStringLiteral(v)) return jsxAttrText(v);
  const x = stripParens(v);
  return ts.isStringLiteralLike(x) ? x.text : null;
}

/**
 * Attributes (props of an HTML/SVG element) with an effect the model does not have, rejected:
 *  - `children`: React renders it as the element's children (on a void element it throws);
 *  - `contentEditable`: the user can then edit the element's content, deleting nodes React
 *    rendered — React's next commit throws (`removeChild` of a node that is no longer there);
 *    `suppressContentEditableWarning` only serves it;
 *  - `is`: a customized built-in element (`<button is="x-btn">`), whose behaviour is defined by
 *    script outside the verified program, like a custom element's;
 *  - a `javascript:` URL written in a URL attribute: its code runs in the page when the link is
 *    followed (React 18 only warns); `srcDoc`, a document whose scripts run with this page's
 *    origin (they can reach `parent.document`);
 *  - `value` / `defaultValue` on an `<input>` that may be `type="file"`, other than "": React
 *    sets the input's value when it mounts or updates it, which throws an InvalidStateError on
 *    a file input.
 * `lname` is the ASCII-lower-cased name: React sets an unknown prop (`contenteditable`) as an
 * attribute, whose name HTML lower-cases.
 */
function checkAttribute(a: ts.JsxAttribute, lname: string, tag: string, e: ts.JsxElement | ts.JsxSelfClosingElement, env: Env) {
  const name = a.name.getText();
  if (lname === "children") fail(a, `${name}={…} is not an attribute: React renders it as the element's children (on a void element such as <input> it throws); write the children between the tags`);
  if (lname === "contenteditable" || lname === "suppresscontenteditablewarning") {
    fail(a, `contentEditable is not supported: the user could then edit the element's content, deleting nodes React rendered, and React's next update throws (removeChild of a node that is gone); use an <input> or a <textarea> for editable text`);
  }
  if (lname === "is") fail(a, `is=… makes a customized built-in element, whose behaviour is defined by script outside the verified program; use a plain HTML element`);
  if (lname === "srcdoc") fail(a, `srcDoc is a document whose scripts run with access to this page (the frame has its origin): code outside the verified program`);
  const lit = literalAttr(a);
  // the URL parser drops leading C0 controls and spaces, and tabs and line breaks anywhere
  if (lit !== null && URL_ATTRS.has(lname) && asciiLower(lit.replace(/^[\x00-\x20]+/, "").replace(/[\t\n\r]/g, "")).startsWith("javascript:")) {
    fail(a, `a javascript: URL runs its code in the page when it is followed: code outside the verified program; use a handler (onClick) instead`);
  }
  if (lname === "name" || lname === "id") checkNamedAccess(a, lname, tag, env);
  if (tag === "input" && (lname === "value" || lname === "defaultvalue")) {
    const types = attrValues(e, "type", env);
    if ((types === undefined || types.includes("file")) && lit !== "") {
      fail(a, `${name} on an <input> that ${types === undefined ? "may be" : "is"} type="file": React sets the input's value when it renders it, which throws on a file input (its value can only be set to ""); ${types === undefined ? "give the input a type that is not \"file\" (a string, or a choice between strings)" : "remove it"}`);
    }
  }
}

/** Elements a form's named getter answers by their `name` and `id`: its listed elements (form-associated custom elements are rejected) and `<img>`. */
const FORM_NAMED = new Set(["button", "fieldset", "input", "object", "output", "select", "textarea", "img"]);
/** Elements the document's named getter answers by their `name` (and the window's, by name). */
const DOC_BY_NAME = new Set(["embed", "form", "iframe", "img", "object"]);
/** Elements the document's named getter answers by their `id` (an `<img>` when it also has a name). */
const DOC_BY_ID = new Set(["object", "img"]);
/** No property name of a form, the document or the window has a character other than these (domNames.ts). */
const PROPERTY_CHARS = /^[A-Za-z0-9_$]*$/;

/**
 * `name` / `id` and HTML's named access (domNames.ts). A form answers `form.x` with its control
 * or image named (or with id) "x", before any property of the form ([LegacyOverrideBuiltIns]),
 * and so does the document with the names of `<embed>`, `<form>`, `<iframe>`, `<img>` and
 * `<object>` and the ids of `<object>` and `<img>`: react-dom reads properties of forms and of
 * the document (`parentNode`, `createElement`, …), and gets the element instead. On these
 * elements every value the attribute may have must be no name the app's code reads, calls or
 * writes there (`reservedName`, on the document when the document exposes the element): a literal,
 * a choice between literals, an enum, a number, or a string built with a literal part holding a
 * character that no property name has (`qty-${id}`); another expression is rejected. The window
 * answers `window.x` only for names it does not define; there the global names the app bundle
 * reads (`windowReserved`) are rejected as written ids; a computed id is not checked (a
 * documented assumption, SEMANTICS §5). `name` on other elements is exposed nowhere.
 */
function checkNamedAccess(a: ts.JsxAttribute, lname: "name" | "id", tag: string, env: Env) {
  const onDoc = (lname === "name" ? DOC_BY_NAME : DOC_BY_ID).has(tag);
  const named = FORM_NAMED.has(tag) || onDoc;
  if (lname === "name" && !named) return;
  const v = attrValue(a);
  if (!v) return; // a boolean attribute: React does not set a name or id given `true`
  const objs = [FORM_NAMED.has(tag) ? "the form it belongs to (a <form> around it, or the one form=… names)" : "", onDoc ? "the document" : ""].filter((x) => x).join(" and of ");
  const there = onDoc ? (FORM_NAMED.has(tag) ? "on forms or on the document" : "on the document") : "on forms";
  const reserved = (x: string) => named && PROPERTY_CHARS.test(x) && reservedName(x, onDoc);
  const reject = (x: string) =>
    fail(a, reserved(x)
      ? `${a.name.getText()}="${x}" on <${tag}>: HTML's named access makes this element the property ${x} of ${objs}, whatever they define, and the app's code uses ${x} ${there} (react-dom reads or calls it, or an effect sets document.title): it would get this element instead (with form.parentNode React loops forever after a click on a radio button, with form.removeChild or document.createElement it throws). Choose another ${lname}, e.g. one with a "-" in it`
      : `${a.name.getText()}="${x}" on <${tag}>: HTML's named access makes this element the global ${x} (window.${x}), which the app's code reads at run time (react-dom, or vreact/spec's runtime); choose another ${lname}`);
  const lits = namedAccessValues(v, env);
  if (lits === undefined) {
    if (!named) return; // a computed id of an element only the window exposes: not checked (SEMANTICS §5)
    fail(a, `${a.name.getText()}={…} on <${tag}>: HTML's named access makes this element the property of ${objs} that its value names, whatever they define, so no value it takes may be a name the app's code uses ${there} (react-dom reads form.parentNode, document.createElement, …), and VTS cannot tell what this one may be. Use a string literal, a choice between literals (c ? "a" : "b"), an enum, a number, or a string with a literal part that holds a character other than letters, digits, _ and $ (\`qty-\${id}\`, "qty-" + id), which no property name has`);
  }
  // the window exposes every element by its id, and <embed>, <form>, <img>, <object> and frames by name
  const onWindow = lname === "id" || DOC_BY_NAME.has(tag);
  for (const x of lits) if (reserved(x) || (onWindow && windowReserved(x))) reject(x);
}

/**
 * The strings an attribute value `x` may set (React sets no attribute for null, undefined or a
 * boolean): the literals; "-" for a number (its decimal digits, a minus sign, "NaN", "Infinity",
 * none of them a property name of a form or the document), and for a string built with a literal
 * part that holds a character outside [A-Za-z0-9_$]; an enum's members. Undefined when unknown.
 */
function namedAccessValues(x0: ts.Expression, env: Env): string[] | undefined {
  const x = stripParens(x0);
  if (ts.isStringLiteral(x) && x.parent && ts.isJsxAttribute(x.parent)) return [jsxAttrText(x)];
  if (ts.isStringLiteralLike(x)) return [x.text];
  if (isNullLit(x, env) || x.kind === ts.SyntaxKind.TrueKeyword || x.kind === ts.SyntaxKind.FalseKeyword) return [];
  if (ts.isConditionalExpression(x)) {
    const l = namedAccessValues(x.whenTrue, env);
    const r = namedAccessValues(x.whenFalse, env);
    return l && r ? [...l, ...r] : undefined;
  }
  if (holdsOtherChar(x)) return ["-"];
  let t: VType;
  try {
    t = typeOf(x, env);
  } catch (err) {
    if (err instanceof VtsError) return undefined;
    throw err;
  }
  if (t.k === "int" || t.k === "num") return ["-", "NaN", "Infinity"];
  if (t.k === "bool") return [];
  if (t.k === "enum") return env.m.reg.enumLits(t);
  return undefined;
}

/** Does every string `x` may be hold a character outside [A-Za-z0-9_$] (written in one of its literal parts)? */
function holdsOtherChar(x0: ts.Expression): boolean {
  const x = stripParens(x0);
  if (ts.isStringLiteralLike(x)) return !PROPERTY_CHARS.test(x.text);
  if (ts.isTemplateExpression(x)) return !PROPERTY_CHARS.test(x.head.text) || x.templateSpans.some((sp) => !PROPERTY_CHARS.test(sp.literal.text));
  if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.PlusToken) return holdsOtherChar(x.left) || holdsOtherChar(x.right);
  if (ts.isConditionalExpression(x)) return holdsOtherChar(x.whenTrue) && holdsOtherChar(x.whenFalse);
  return false;
}

/** Elements returned by `xs.map(…)`, whose key is translated (as the key function) by `keyedMap`. */
const keyedByMap = new WeakSet<ts.Node>();

/**
 * The last translation of each `key={…}` (by `keyExpr`), read right after the translation of its
 * element (`translatedKey`): the keys of siblings are these terms, with their obligations.
 */
const keyVals = new WeakMap<ts.JsxAttribute, Val>();

/** The translation of the element's `key={…}` its translation just made (undefined: no key, or one written as a string). */
function translatedKey(e: ts.Expression): Val | undefined {
  if (!(ts.isJsxElement(e) || ts.isJsxSelfClosingElement(e))) return undefined;
  const a = keyAttrOf(e);
  return a ? keyVals.get(a) : undefined;
}

/** The translated `key={…}` of an element outside a keyed map: JS evaluates it on every render, so its obligations count. */
function keyExpr(a: ts.JsxAttribute, e: ts.Node, env: Env): string | null {
  if (keyedByMap.has(e)) return null;
  const val = attrValue(a);
  if (!val) fail(a, "key needs a value");
  keyVals.delete(a);
  if (ts.isStringLiteral(val)) return null;
  const v = expr(val, env);
  keyVals.set(a, v);
  return v.code;
}

function withKey(key: string | null, node: string): string {
  return key === null ? node : `(VReact.VNode.withKey ${paren(key)}\n  ${node})`;
}

/**
 * A component that renders (or otherwise refers to) itself: recursion, which VTS does not
 * support. React would render one more instance per level (a recursion without a base case
 * never ends), and the model has no recursive components.
 */
export function selfRenderMsg(name: string, what: string): string {
  return `${what} inside ${name}: a component that refers to itself (renders itself, directly or through a JSX constant, a map callback or a branch) is recursion, which is not supported yet; flatten the nested data into an array (e.g. rows with a depth field) and render it with map`;
}

function componentElement(tagNode: ts.JsxTagNameExpression, e: ts.JsxElement | ts.JsxSelfClosingElement, kids: ts.NodeArray<ts.JsxChild> | undefined, env: Env): string {
  const m = env.m;
  // its elements would be created in the enclosing <svg>'s (<math>'s) namespace, while it is
  // checked as the root of an HTML tree
  if (bubble.ns === "svg" || bubble.ns === "math") fail(e, `<${tagNode.getText()}> inside <${bubble.ns}>: React would create its elements in the ${bubble.ns === "svg" ? "SVG" : "MathML"} namespace (an <input> there is no HTML control), while it is verified as HTML; render the component outside the <${bubble.ns}>${bubble.ns === "svg" ? ", or inside a <foreignObject>" : ""}`);
  if (bubble.content !== null) failContent(e, `<${tagNode.getText()}>`, bubble.content, true);
  if (bubble.handlers.length) fail(e, `<${tagNode.getText()}> is nested inside an element with ${bubble.handlers.join("/")}: its events would bubble into a second handler (move the handler, or the component, out)`);
  if (bubble.act) fail(e, `<${tagNode.getText()}> is nested inside ${bubble.act.what}: a click inside it would run its handlers and, through the activation of the enclosing element, another one, in one batch when a script dispatches the click (move the component out${bubble.act.label ? "; a label can name a control inside it with htmlFor" : ""})`);
  let sym = m.checker.getSymbolAtLocation(tagNode);
  if (sym && sym.flags & ts.SymbolFlags.Alias) sym = m.checker.getAliasedSymbol(sym);
  const g = sym?.declarations?.[0] ? m.prog.globals.get(sym.declarations[0]) : undefined;
  if (!g || g.k !== "comp") fail(tagNode, `<${tagNode.getText()}> is not a verified component (declare it in a VTS module, or mark it @trusted)`);
  const info = g.info;
  // (module.ts rejects every reference of a component to itself before the translation: backstop)
  if (env.comp?.info === info) fail(tagNode, selfRenderMsg(info.name, `<${tagNode.getText()}>`));
  if (kids && kids.some((k) => !(ts.isJsxText(k) && !jsxTextValue(k.text, k)))) fail(e, "children of user components are not supported yet");
  const given = new Map<string, ts.JsxAttribute>();
  for (const a of attrs(e)) {
    if (ts.isJsxSpreadAttribute(a)) fail(a, "spread props are not supported");
    if (a.name.getText() === "ref") fail(a, "ref is not supported in VTS (refs are not modelled; React 18 does not pass them to function components)");
    if (RESERVED_PROPS.includes(a.name.getText())) fail(a, `${a.name.getText()} cannot be passed as a prop: ${RESERVED_WHY(a.name.getText())}`);
    if (given.has(a.name.getText())) fail(a, `${a.name.getText()} is given twice`);
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

/**
 * For a list of a Map's values (`[...m.values()]`, `Array.from(m.values())`) keyed by a field of
 * the value: the usual ways to prove the keys distinct, for the failure report.
 */
function mapValuesKeyHint(list: ts.Expression, keyE: ts.Expression, env: Env): string {
  let e = stripParens(list);
  if (ts.isArrayLiteralExpression(e) && e.elements.length === 1 && ts.isSpreadElement(e.elements[0])) e = stripParens(e.elements[0].expression);
  else if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.name.text === "from" && e.arguments.length === 1) e = stripParens(e.arguments[0]);
  else return "";
  if (!ts.isCallExpression(e) || !ts.isPropertyAccessExpression(e.expression) || e.expression.name.text !== "values") return "";
  const recv = e.expression.expression;
  const ck = env.m.checker;
  if (collectionKind(ck.getNonNullableType(ck.getTypeAtLocation(recv)), env.m.prog.typeEnv) !== "map") return "";
  const mt = nodeText(recv, 30);
  return ` (for the values of a Map: key by the Map key, [...${mt}].map(([k, v]) => <… key={k}>), or add [...${mt}].every(([k, v]) => v.${ts.isPropertyAccessExpression(keyE) ? keyE.name.text : "id"} === k) to the invariant)`;
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
    // an enum member is its string (React sees exactly that string), as in `${k}`
    if (kv.type.k === "enum") return `VReact.Key.str (VReact.JS.str ${paren(kv.code)})`;
    fail(keyE, "keys must be int, string or a string-literal enum");
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
  const ob = m.ob(keyAttr, "unique-keys", `keys ${nodeText(keyE)} are distinct across ${nodeText(pa.expression)}${mapValuesKeyHint(pa.expression, keyE, env)}`);
  return `(VReact.VNode.keyedMap ${paren(xs.code)} (fun ${kEnvR.binder} => ${keyCode})\n  (fun ${nEnvR.binder} ${hm} => ${nodeCode})\n  ${ob})`;
}
