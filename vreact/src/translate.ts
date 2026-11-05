/**
 * VTS → Lean translation.
 *
 * Semantics-by-translation: every accepted TypeScript construct is mapped to a
 * Lean term whose value is the JavaScript value of the construct.  Operations
 * that can fail at runtime carry an inline proof obligation `(by vreact_auto)`.
 *
 * Statements are translated in continuation-passing style: `block(stmts, env, k)`
 * produces a Lean term for the statements followed by the continuation `k`.
 * Local mutation (`let x = …; x = …`) becomes shadowing `let`s; branches
 * duplicate the continuation; `for…of` loops become folds.
 */
import ts from "typescript";
import { T, type VType, type Field, type Param, sameType, showType, leanType, sharedFields, type Variant, typeOfNode } from "./types.ts";
import { type Env, type Val, ModCtx, type Binding, type StateVar, type CompCtx, type HandlerAcc, type FnInfo, type CompInfo, type Global, type Narrowed, bind, extend, freshLocal } from "./ctx.ts";
import { fail, leanField, leanIdent, leanStr, jsStr, leanInt, paren, nodeText, capitalize } from "./util.ts";

/* ───────────────────────────── helpers ───────────────────────────── */

const symIds = new WeakMap<ts.Symbol, number>();
let symCounter = 0;
function symId(s: ts.Symbol): number {
  let id = symIds.get(s);
  if (id === undefined) {
    id = ++symCounter;
    symIds.set(s, id);
  }
  return id;
}

export function symbolOf(env: Env, node: ts.Node): ts.Symbol | undefined {
  if (ts.isShorthandPropertyAssignment(node)) return env.m.checker.getShorthandAssignmentValueSymbol(node);
  return env.m.checker.getSymbolAtLocation(node);
}

function resolved(env: Env, s: ts.Symbol | undefined): ts.Symbol | undefined {
  if (s && s.flags & ts.SymbolFlags.Alias) return env.m.checker.getAliasedSymbol(s);
  return s;
}

/** Name of a `vreact/spec` function if `callee` refers to one. */
export function specFn(env: Env, callee: ts.Expression): string | null {
  if (!ts.isIdentifier(callee)) return null;
  const s = resolved(env, symbolOf(env, callee));
  const d = s?.declarations?.[0];
  if (d && /vreact[\\/](spec|lib)|vreact-spec/.test(d.getSourceFile().fileName)) return s!.name;
  return null;
}

const HOOKS = new Set(["useState", "useReducer", "useEffect", "useMemo", "useCallback", "useRef", "useContext", "useLayoutEffect", "useId", "useTransition", "useDeferredValue", "useSyncExternalStore", "useImperativeHandle"]);

/** Name of a React hook if `callee` refers to one. */
export function hookName(env: Env, callee: ts.Expression): string | null {
  let name: string | null = null;
  if (ts.isIdentifier(callee)) name = callee.text;
  else if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) && callee.expression.text === "React") name = callee.name.text;
  if (!name || !HOOKS.has(name)) return null;
  const s = resolved(env, symbolOf(env, ts.isPropertyAccessExpression(callee) ? callee.name : callee));
  const d = s?.declarations?.[0];
  if (d && /node_modules[\\/](@types[\\/])?react[\\/]/.test(d.getSourceFile().fileName)) return name;
  return name; // be permissive: a user function called use* is treated as a hook too
}

function globalOf(env: Env, node: ts.Node): Global | undefined {
  const s = resolved(env, symbolOf(env, node));
  const d = s?.declarations?.[0];
  if (!d) return undefined;
  return env.m.prog.globals.get(d);
}

/** Path key for narrowing (identifier or property chain). */
function pathKey(env: Env, e: ts.Expression): string | null {
  if (ts.isParenthesizedExpression(e)) return pathKey(env, e.expression);
  if (ts.isIdentifier(e)) {
    const s = symbolOf(env, e);
    return s ? `#${symId(s)}` : null;
  }
  if (ts.isPropertyAccessExpression(e) && !e.questionDotToken) {
    const k = pathKey(env, e.expression);
    return k ? `${k}.${e.name.text}` : null;
  }
  return null;
}

function isNullLit(e: ts.Expression): boolean {
  return e.kind === ts.SyntaxKind.NullKeyword || (ts.isIdentifier(e) && e.text === "undefined");
}

function stripParens(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) && e.type.getText() === "const") e = ts.isParenthesizedExpression(e) ? e.expression : (e as ts.AsExpression).expression;
  return e;
}

function isIntLike(t: VType) {
  return t.k === "int";
}
function isNumeric(t: VType) {
  return t.k === "int" || t.k === "num";
}

/** Insert a coercion from `v.type` to `expected` where VTS allows one. */
export function coerce(v: Val, expected: VType | undefined, node: ts.Node, env: Env): Val {
  if (!expected || sameType(v.type, expected)) return v;
  if (expected.k === "num" && v.type.k === "int") return { code: `(Float.ofInt ${paren(v.code)})`, type: T.num };
  if (expected.k === "opt" && sameType(v.type, expected.elem)) return { code: `(some ${paren(v.code)})`, type: expected };
  if (expected.k === "opt" && v.type.k === "int" && expected.elem.k === "num") return { code: `(some (Float.ofInt ${paren(v.code)}))`, type: expected };
  if (expected.k === "arr" && v.type.k === "arr" && v.code === "[]") return { code: "[]", type: expected };
  if (expected.k === "void" || expected.k === "unit") return v;
  fail(node, `type mismatch: expected ${showType(expected)}, got ${showType(v.type)}`);
}

/* ───────────────────────────── expressions ───────────────────────────── */

export function expr(e: ts.Expression, env: Env, expected?: VType): Val {
  const v = expr0(e, env, expected);
  return coerce(v, expected, e, env);
}

function expr0(e: ts.Expression, env: Env, expected?: VType): Val {
  const m = env.m;
  // narrowed path?
  const key = pathKey(env, e);
  if (key) {
    const n = env.narrow.get(key);
    if (n && n.kind === "some") return { code: n.code, type: n.type };
  }
  switch (e.kind) {
    case ts.SyntaxKind.ParenthesizedExpression:
      return expr((e as ts.ParenthesizedExpression).expression, env, expected);
    case ts.SyntaxKind.NumericLiteral: {
      const text = (e as ts.NumericLiteral).text;
      if (expected?.k === "num" || /[.eE]/.test(text)) return { code: `(${text} : Float)`, type: T.num };
      return { code: leanInt(BigInt(text)), type: T.int };
    }
    case ts.SyntaxKind.StringLiteral:
    case ts.SyntaxKind.NoSubstitutionTemplateLiteral: {
      const text = (e as ts.StringLiteral).text;
      if (expected?.k === "enum") {
        const lits = m.reg.enumLits(expected);
        if (!lits.includes(text)) fail(e, `"${text}" is not a member of ${showType(expected)}`);
        return { code: `${expected.name}.${leanField(text)}`, type: expected };
      }
      if (expected?.k === "opt" && expected.elem.k === "enum") return expr0(e, env, expected.elem);
      return { code: jsStr(text), type: T.str };
    }
    case ts.SyntaxKind.TrueKeyword:
      return { code: "true", type: T.bool };
    case ts.SyntaxKind.FalseKeyword:
      return { code: "false", type: T.bool };
    case ts.SyntaxKind.NullKeyword:
      if (!expected || expected.k !== "opt") fail(e, "null needs an expected type T | null");
      return { code: "none", type: expected };
    case ts.SyntaxKind.Identifier:
      return identifier(e as ts.Identifier, env, expected);
    case ts.SyntaxKind.PropertyAccessExpression:
      return propertyAccess(e as ts.PropertyAccessExpression, env);
    case ts.SyntaxKind.ElementAccessExpression:
      return elementAccess(e as ts.ElementAccessExpression, env);
    case ts.SyntaxKind.CallExpression:
      return call(e as ts.CallExpression, env, expected);
    case ts.SyntaxKind.BinaryExpression:
      return binary(e as ts.BinaryExpression, env, expected);
    case ts.SyntaxKind.PrefixUnaryExpression:
      return prefix(e as ts.PrefixUnaryExpression, env, expected);
    case ts.SyntaxKind.ConditionalExpression: {
      const c = e as ts.ConditionalExpression;
      let ty: VType | undefined = expected;
      if (!ty && (isNullLit(stripParens(c.whenTrue)) || isNullLit(stripParens(c.whenFalse)))) {
        // type the non-null branch in its (narrowed) environment, without emitting anything
        let ot: VType | undefined;
        const dry = { ...env, m: dryCtx(env.m) };
        branch(c.condition, dry, (e1) => {
          if (!isNullLit(stripParens(c.whenTrue))) ot = typeOf(c.whenTrue, e1);
          return "_";
        }, (e2) => {
          if (!isNullLit(stripParens(c.whenFalse))) ot = typeOf(c.whenFalse, e2);
          return "_";
        });
        if (ot) ty = ot.k === "opt" ? ot : T.opt(ot);
      }
      const code = branch(c.condition, env, (e1) => {
        const v = expr(c.whenTrue, e1, ty);
        ty = ty ?? v.type;
        return v.code;
      }, (e2) => {
        const v = expr(c.whenFalse, e2, ty);
        ty = ty ?? v.type;
        return v.code;
      });
      return { code, type: ty! };
    }
    case ts.SyntaxKind.TemplateExpression: {
      const te = e as ts.TemplateExpression;
      const parts: string[] = [];
      if (te.head.text) parts.push(jsStr(te.head.text));
      for (const span of te.templateSpans) {
        parts.push(toStr(expr(span.expression, env), span.expression));
        if (span.literal.text) parts.push(jsStr(span.literal.text));
      }
      return { code: parts.length ? `(${parts.join(" ++ ")})` : jsStr(""), type: T.str };
    }
    case ts.SyntaxKind.ObjectLiteralExpression:
      return objectLiteral(e as ts.ObjectLiteralExpression, env, expected);
    case ts.SyntaxKind.ArrayLiteralExpression:
      return arrayLiteral(e as ts.ArrayLiteralExpression, env, expected);
    case ts.SyntaxKind.AsExpression: {
      const a = e as ts.AsExpression;
      if (a.type.getText() === "const") return expr(a.expression, env, expected);
      fail(e, "type assertions (`as`) are not allowed in VTS: they are unchecked casts");
    }
    case ts.SyntaxKind.NonNullExpression: {
      const inner = expr((e as ts.NonNullExpression).expression, env);
      if (inner.type.k !== "opt") fail(e, "`!` applied to a non-optional value");
      const ob = m.ob(e, "non-null", `\`${nodeText(e)}\` is not null/undefined`);
      return { code: `(Option.get ${paren(inner.code)} ${ob})`, type: inner.type.elem };
    }
    case ts.SyntaxKind.ArrowFunction:
    case ts.SyntaxKind.FunctionExpression:
      fail(e, "function values may only appear as event handlers, callbacks, or array-method arguments");
    case ts.SyntaxKind.JsxElement:
    case ts.SyntaxKind.JsxSelfClosingElement:
    case ts.SyntaxKind.JsxFragment:
      fail(e, "JSX is only allowed in the value returned by a component");
    default:
      fail(e, `expression not supported in VTS: ${nodeText(e)}`);
  }
}

/** Conversion to string (template literals, JSX text, string concatenation). */
function toStr(v: Val, node: ts.Node): string {
  switch (v.type.k) {
    case "str":
      return paren(v.code);
    case "int":
    case "num":
    case "bool":
    case "enum":
      return `(VReact.JS.str ${paren(v.code)})`;
    default:
      fail(node, `cannot convert ${showType(v.type)} to a string`);
  }
}

function identifier(id: ts.Identifier, env: Env, expected?: VType, symOverride?: ts.Symbol): Val {
  if (id.text === "undefined") {
    if (!expected || expected.k !== "opt") fail(id, "undefined needs an expected type T | undefined");
    return { code: "none", type: expected };
  }
  const s = symOverride ?? symbolOf(env, id);
  const b = s ? env.vars.get(s) : undefined;
  if (s && !symOverride) {
    const n = env.narrow.get(`#${symId(s)}`);
    if (n && n.kind === "some") return { code: n.code, type: n.type };
  }
  if (b) {
    if (b.k === "val") return { code: b.code, type: b.type };
    if (b.k === "props") fail(id, "the props object can only be used through its fields (props.x)");
    if (b.k === "setter" || b.k === "dispatch") fail(id, "setters/dispatch may only be called inside event handlers and effects");
    if (b.k === "callback") fail(id, "callback props may only be called (in handlers) or passed to child components");
    if (b.k === "closure") fail(id, "a function value can only be called, or used as an event handler / callback");
    if (b.k === "event") fail(id, "the event object can only be used through e.target.value / e.target.checked / e.key");
    if (b.k === "jsx") fail(id, "JSX values can only appear inside JSX");
  }
  const g = s && symOverride ? (() => { const d = resolved(env, s)?.declarations?.[0]; return d ? env.m.prog.globals.get(d) : undefined; })() : globalOf(env, id);
  if (g?.k === "const") {
    env.m.deps.add(g.info.qname);
    return { code: g.info.qname, type: g.info.type };
  }
  if (g?.k === "fn") fail(id, "functions are not first-class in VTS; call the function instead");
  fail(id, `unknown or unsupported identifier \`${id.text}\` (only locals, props, state, and verified top-level declarations can be referenced)`);
}

function propertyAccess(pa: ts.PropertyAccessExpression, env: Env): Val {
  const m = env.m;
  const name = pa.name.text;
  // event fields: e.target.value / e.currentTarget.value / e.target.checked / e.key
  const evVar = eventBase(pa, env);
  if (evVar) return evVar;
  // props.x
  if (ts.isIdentifier(pa.expression)) {
    const s = symbolOf(env, pa.expression);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "props") {
      const comp = env.comp!;
      const f = comp.info.data.find((f) => f.name === name);
      if (f) return { code: `${comp.propsVar}.${leanField(name)}`, type: f.type };
      fail(pa, `props.${name} is a callback: it can only be called in a handler or passed to a child`);
    }
  }
  // optional chaining x?.f
  if (pa.questionDotToken) {
    const base = expr(pa.expression, env);
    if (base.type.k !== "opt") fail(pa, "?. on a non-optional value");
    const { name: v } = freshLocal(env, "v");
    const inner = fieldOf({ code: v, type: base.type.elem }, name, pa, env);
    if (inner.type.k === "opt") return { code: `(Option.bind ${paren(base.code)} (fun ${v} => ${inner.code}))`, type: inner.type };
    return { code: `(Option.map (fun ${v} => ${inner.code}) ${paren(base.code)})`, type: T.opt(inner.type) };
  }
  // narrowed union variant field
  const baseKey = pathKey(env, pa.expression);
  if (baseKey) {
    const n = env.narrow.get(baseKey);
    if (n && n.kind === "variant") {
      const u = m.reg.union(n.type);
      if (name === u.tag) return { code: jsStr(n.variant!), type: T.str };
      const f = n.fields!.get(name);
      if (f) return f;
    }
  }
  const base = expr(pa.expression, env);
  return fieldOf(base, name, pa, env);
}

function eventBase(pa: ts.PropertyAccessExpression, env: Env): Val | null {
  // e.key
  const root = (x: ts.Expression): Binding | undefined => {
    if (!ts.isIdentifier(x)) return undefined;
    const s = symbolOf(env, x);
    return s ? env.vars.get(s) : undefined;
  };
  const b1 = root(pa.expression);
  if (b1?.k === "event") {
    if (pa.name.text === "key") return { code: `${b1.leanVar}.key`, type: T.str };
    fail(pa, `unsupported event property e.${pa.name.text} (supported: e.key, e.target.value, e.target.checked)`);
  }
  if (ts.isPropertyAccessExpression(pa.expression)) {
    const b2 = root(pa.expression.expression);
    if (b2?.k === "event" && ["target", "currentTarget"].includes(pa.expression.name.text)) {
      if (pa.name.text === "value") return { code: `${b2.leanVar}.value`, type: T.str };
      if (pa.name.text === "checked") return { code: `${b2.leanVar}.checked`, type: T.bool };
      fail(pa, `unsupported event property (supported: e.target.value, e.target.checked)`);
    }
  }
  return null;
}

function fieldOf(base: Val, name: string, node: ts.Node, env: Env): Val {
  const m = env.m;
  const t = base.type;
  if (t.k === "arr" && name === "length") return { code: `(${paren(base.code)}.length : Int)`, type: T.int };
  if (t.k === "str" && name === "length") return { code: `(VReact.JS.strLen ${paren(base.code)})`, type: T.int };
  if (t.k === "rec") {
    const f = m.reg.rec(t).find((f) => f.name === name);
    if (!f) fail(node, `no field ${name} in ${showType(t)}`);
    return { code: `${paren(base.code)}.${leanField(name)}`, type: f.type };
  }
  if (t.k === "union") {
    const u = m.reg.union(t);
    if (name === u.tag) return { code: `(${t.name}.${leanField(name)} ${paren(base.code)})`, type: T.str };
    const sf = sharedFields(u.variants).find((f) => f.name === name);
    if (sf) return { code: `(${t.name}.${leanField(name)} ${paren(base.code)})`, type: sf.type };
    fail(node, `field ${name} is not present in every variant of ${showType(t)}: narrow first (if (x.${u.tag} === "…"))`);
  }
  if (t.k === "tuple") fail(node, "use index access t[0] on tuples");
  if (t.k === "opt") fail(node, `\`${name}\` accessed on a possibly-null value: narrow with !== null first`);
  fail(node, `property ${name} not supported on ${showType(t)}`);
}

function elementAccess(ea: ts.ElementAccessExpression, env: Env): Val {
  const base = expr(ea.expression, env);
  const arg = ea.argumentExpression;
  if (base.type.k === "tuple") {
    if (!ts.isNumericLiteral(arg)) fail(arg, "tuple index must be a literal");
    const i = Number(arg.text);
    const n = base.type.elems.length;
    if (i >= n) fail(arg, "tuple index out of range");
    let code = paren(base.code);
    for (let j = 0; j < i; j++) code = `${code}.2`;
    if (i < n - 1) code = `${code}.1`;
    return { code, type: base.type.elems[i] };
  }
  if (base.type.k !== "arr") fail(ea, `indexing is only supported on arrays and tuples`);
  const idx = expr(arg, env, T.int);
  const ob = env.m.ob(ea, "index", `index ${nodeText(arg)} is within bounds of ${nodeText(ea.expression)}`);
  return { code: `(VReact.JS.get ${paren(base.code)} ${paren(idx.code)} ${ob})`, type: base.type.elem };
}

function prefix(p: ts.PrefixUnaryExpression, env: Env, expected?: VType): Val {
  switch (p.operator) {
    case ts.SyntaxKind.ExclamationToken: {
      const v = expr(p.operand, env, T.bool);
      return { code: `(!${paren(v.code)})`, type: T.bool };
    }
    case ts.SyntaxKind.MinusToken: {
      if (ts.isNumericLiteral(p.operand)) {
        const v = expr(p.operand, env, expected);
        return { code: v.type.k === "int" ? `(-${v.code})` : `(-${v.code})`, type: v.type };
      }
      const v = expr(p.operand, env);
      if (!isNumeric(v.type)) fail(p, "unary minus on a non-number");
      return { code: `(-${paren(v.code)})`, type: v.type };
    }
    case ts.SyntaxKind.PlusToken:
      return expr(p.operand, env, expected);
    default:
      fail(p, "++/-- are only allowed as statements on local `let` variables");
  }
}

function isEqOp(k: ts.SyntaxKind) {
  return k === ts.SyntaxKind.EqualsEqualsEqualsToken || k === ts.SyntaxKind.EqualsEqualsToken;
}
function isNeqOp(k: ts.SyntaxKind) {
  return k === ts.SyntaxKind.ExclamationEqualsEqualsToken || k === ts.SyntaxKind.ExclamationEqualsToken;
}

function binary(b: ts.BinaryExpression, env: Env, expected?: VType): Val {
  const op = b.operatorToken.kind;
  const K = ts.SyntaxKind;
  if (op === K.AmpersandAmpersandToken || op === K.BarBarToken) {
    if (hasNarrowing(b.left, env) || hasNarrowing(b.right, env)) {
      return { code: branch(b, env, () => "true", () => "false"), type: T.bool };
    }
    const l = expr(b.left, env, T.bool);
    const before = env.m.obCount();
    const r = expr(b.right, env, T.bool);
    if (env.m.obCount() > before) {
      // the right operand needs the left one as a hypothesis (short-circuit)
      const h = env.m.fresh("h");
      return op === K.AmpersandAmpersandToken
        ? { code: `(if ${h} : ${paren(l.code)} = true then ${paren(r.code)} else false)`, type: T.bool }
        : { code: `(if ${h} : ${paren(l.code)} = true then true else ${paren(r.code)})`, type: T.bool };
    }
    return { code: `(${paren(l.code)} ${op === K.AmpersandAmpersandToken ? "&&" : "||"} ${paren(r.code)})`, type: T.bool };
  }
  if (op === K.QuestionQuestionToken) {
    const l = expr(b.left, env);
    if (l.type.k !== "opt") fail(b, "?? on a non-optional value");
    if (isNullLit(stripParens(b.right))) return l;
    const r = expr(b.right, env, l.type.elem);
    return { code: `(Option.getD ${paren(l.code)} ${paren(r.code)})`, type: l.type.elem };
  }
  if (op === K.EqualsToken || op === K.PlusEqualsToken || op === K.MinusEqualsToken) {
    fail(b, "assignments are statements in VTS (and only to local `let` variables)");
  }
  if (isEqOp(op) || isNeqOp(op)) {
    if (op === K.EqualsEqualsToken || op === K.ExclamationEqualsToken) {
      if (!isNullLit(b.left) && !isNullLit(b.right)) fail(b, "use === / !== (loose equality is only allowed against null)");
    }
    const neg = isNeqOp(op);
    if (isNullLit(b.right) || isNullLit(b.left)) {
      const other = isNullLit(b.right) ? b.left : b.right;
      const v = expr(other, env);
      if (v.type.k !== "opt") fail(b, "comparison with null/undefined of a non-optional value");
      return { code: neg ? `(Option.isSome ${paren(v.code)})` : `(Option.isNone ${paren(v.code)})`, type: T.bool };
    }
    let l = expr(b.left, env);
    let r = expr(b.right, env, l.type.k === "enum" || l.type.k === "opt" ? l.type : undefined);
    if (l.type.k === "str" && r.type.k === "enum") l = expr(b.left, env, r.type);
    if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, b, env);
    if (r.type.k === "int" && l.type.k === "num") r = coerce(r, T.num, b, env);
    if (!sameType(l.type, r.type)) fail(b, `comparing ${showType(l.type)} with ${showType(r.type)}`);
    if (["rec", "arr", "union", "tuple"].includes(l.type.k)) {
      fail(b, `=== on ${showType(l.type)} compares object identity in JS; compare keys/fields instead`);
    }
    const eq = l.type.k === "num" ? `(${paren(l.code)} == ${paren(r.code)})` : `(VReact.JS.eq ${paren(l.code)} ${paren(r.code)})`;
    return { code: neg ? `(!${eq})` : eq, type: T.bool };
  }
  const cmp: Record<number, string> = {
    [K.LessThanToken]: "<",
    [K.LessThanEqualsToken]: "≤",
    [K.GreaterThanToken]: ">",
    [K.GreaterThanEqualsToken]: "≥",
  };
  if (cmp[op]) {
    let l = expr(b.left, env);
    let r = expr(b.right, env, l.type);
    if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, b, env);
    if (!isNumeric(l.type) && l.type.k !== "str") fail(b, "ordering comparison on non-numbers");
    if (l.type.k === "str") fail(b, "string ordering comparisons are not supported (use localeCompare-free logic)");
    // instance-free Bool comparisons (simp rewrites their arguments freely; see JS.lt_iff)
    const fn = { "<": ["lt", false], "≤": ["le", false], ">": ["lt", true], "≥": ["le", true] }[cmp[op]] as [string, boolean];
    const [a, bb] = fn[1] ? [r.code, l.code] : [l.code, r.code];
    return { code: `(VReact.JS.${fn[0]} ${paren(a)} ${paren(bb)})`, type: T.bool };
  }
  if (op === K.PlusToken) {
    const l = expr(b.left, env, expected?.k === "str" ? undefined : expected);
    const r = expr(b.right, env, l.type.k === "str" ? undefined : l.type);
    if (l.type.k === "str" || r.type.k === "str") {
      return { code: `(${toStr(l, b.left)} ++ ${toStr(r, b.right)})`, type: T.str };
    }
    return arith("+", l, r, b, env);
  }
  if (op === K.MinusToken || op === K.AsteriskToken) {
    const l = expr(b.left, env, expected);
    const r = expr(b.right, env, l.type);
    return arith(op === K.MinusToken ? "-" : "*", l, r, b, env);
  }
  if (op === K.SlashToken) {
    let l = expr(b.left, env);
    let r = expr(b.right, env);
    // int / int is a JS number (no integer division); Math.floor(a / b) is handled at the call.
    l = coerce(l, T.num, b, env);
    r = coerce(r, T.num, b, env);
    return { code: `(${paren(l.code)} / ${paren(r.code)})`, type: T.num };
  }
  if (op === K.PercentToken) {
    const l = expr(b.left, env, T.int);
    const r = expr(b.right, env, T.int);
    const ob = env.m.ob(b, "nonzero-divisor", `divisor ${nodeText(b.right)} is non-zero`);
    return { code: `(VReact.JS.rem ${paren(l.code)} ${paren(r.code)} ${ob})`, type: T.int };
  }
  fail(b, `operator ${b.operatorToken.getText()} not supported in VTS`);
}

function arith(op: string, l: Val, r: Val, node: ts.Node, env: Env): Val {
  if (!isNumeric(l.type) || !isNumeric(r.type)) fail(node, `arithmetic on ${showType(l.type)} and ${showType(r.type)}`);
  if (l.type.k === "num" || r.type.k === "num") {
    l = coerce(l, T.num, node, env);
    r = coerce(r, T.num, node, env);
    return { code: `(${paren(l.code)} ${op} ${paren(r.code)})`, type: T.num };
  }
  return { code: `(${paren(l.code)} ${op} ${paren(r.code)})`, type: T.int };
}

/* ─────────────────────── object & array literals ─────────────────────── */

function objectLiteral(o: ts.ObjectLiteralExpression, env: Env, expected?: VType): Val {
  const m = env.m;
  if (!expected) fail(o, "object literal needs a known type (annotate the variable / function return type)");
  if (expected.k === "opt") return coerce(objectLiteral(o, env, expected.elem), expected, o, env);
  const props = new Map<string, ts.Expression | ts.ShorthandPropertyAssignment>();
  let spread: ts.Expression | null = null;
  for (const p of o.properties) {
    if (ts.isPropertyAssignment(p)) props.set(p.name.getText().replace(/^["']|["']$/g, ""), p.initializer);
    else if (ts.isShorthandPropertyAssignment(p)) props.set(p.name.text, p);
    else if (ts.isSpreadAssignment(p)) {
      if (spread || props.size) fail(p, "a spread must come first in an object literal ({ ...x, f: v })");
      spread = p.expression;
    } else fail(p, "only `f: e`, shorthand `f`, and a leading spread are allowed in object literals");
  }
  const valOf = (p: ts.Expression | ts.ShorthandPropertyAssignment, t: VType): Val => {
    if (ts.isShorthandPropertyAssignment(p)) {
      const vs = env.m.checker.getShorthandAssignmentValueSymbol(p);
      const key = vs ? `#${symId(vs)}` : null;
      const n = key ? env.narrow.get(key) : undefined;
      if (n && n.kind === "some") return coerce({ code: n.code, type: n.type }, t, p, env);
      return coerce(identifier(p.name, env, t, vs), t, p, env);
    }
    return expr(p, env, t);
  };
  if (expected.k === "rec") {
    const fields = m.reg.rec(expected);
    for (const k of props.keys()) if (!fields.some((f) => f.name === k)) fail(o, `unknown field ${k} for ${showType(expected)}`);
    if (spread) {
      const base = expr(spread, env, expected);
      // nested single-field updates (layout-insensitive)
      let code = paren(base.code);
      for (const [k, p] of props) {
        code = `({ ${code} with ${leanField(k)} := ${paren(valOf(p, fields.find((f) => f.name === k)!.type).code)} } : ${expected.name})`;
      }
      return { code, type: expected };
    }
    const parts = fields.map((f) => {
      const p = props.get(f.name);
      if (!p) {
        if (f.type.k === "opt") return "none";
        fail(o, `missing field ${f.name} of ${showType(expected)}`);
      }
      return paren(valOf(p, f.type).code);
    });
    return { code: `(${expected.name}.mk${parts.map((x) => " " + x).join("")})`, type: expected };
  }
  if (expected.k === "union") {
    const u = m.reg.union(expected);
    if (spread) fail(o, "spreads are not supported for union values; construct the variant explicitly");
    const tagExpr = props.get(u.tag);
    if (!tagExpr || ts.isShorthandPropertyAssignment(tagExpr) || !ts.isStringLiteralLike(stripParens(tagExpr))) {
      fail(o, `union literal needs a literal discriminant ${u.tag}: "…"`);
    }
    const lit = (stripParens(tagExpr) as ts.StringLiteral).text;
    const v = u.variants.find((v) => v.lit === lit);
    if (!v) fail(o, `"${lit}" is not a variant of ${showType(expected)}`);
    for (const k of props.keys()) if (k !== u.tag && !v.fields.some((f) => f.name === k)) fail(o, `unknown field ${k} for variant ${lit}`);
    const args = v.fields.map((f) => {
      const p = props.get(f.name);
      if (!p) {
        if (f.type.k === "opt") return "none";
        fail(o, `missing field ${f.name} of variant ${lit}`);
      }
      return paren(valOf(p, f.type).code);
    });
    return { code: `(${expected.name}.${leanField(v.ctor)}${args.map((a) => " " + a).join("")})`, type: expected };
  }
  fail(o, `object literal where ${showType(expected)} was expected`);
}

function arrayLiteral(a: ts.ArrayLiteralExpression, env: Env, expected?: VType): Val {
  if (expected?.k === "tuple") {
    if (a.elements.length !== expected.elems.length) fail(a, "tuple arity mismatch");
    return { code: `(${a.elements.map((e, i) => expr(e, env, expected.elems[i]).code).join(", ")})`, type: expected };
  }
  let elemT: VType | undefined = expected?.k === "arr" ? expected.elem : expected?.k === "opt" && expected.elem.k === "arr" ? expected.elem.elem : undefined;
  const pieces: string[] = [];
  let group: string[] = [];
  const flush = () => {
    if (group.length) pieces.push(`[${group.join(", ")}]`);
    group = [];
  };
  for (const el of a.elements) {
    if (ts.isSpreadElement(el)) {
      const v = expr(el.expression, env, elemT ? T.arr(elemT) : undefined);
      if (v.type.k !== "arr") fail(el, "spread of a non-array");
      elemT = elemT ?? v.type.elem;
      flush();
      pieces.push(paren(v.code));
    } else {
      const v = expr(el, env, elemT);
      elemT = elemT ?? v.type;
      group.push(v.code);
    }
  }
  flush();
  if (!elemT) fail(a, "empty array literal needs a known element type (annotate it)");
  const code = pieces.length === 0 ? "[]" : pieces.length === 1 ? pieces[0] : `(${pieces.join(" ++ ")})`;
  return { code: pieces.length === 0 ? `([] : List ${leanType(elemT)})` : code, type: T.arr(elemT) };
}

/* ───────────────────────────── calls ───────────────────────────── */

/** Translate an arrow function used as a pure lambda (array methods). */
export function lambda(
  fn: ts.Expression,
  env: Env,
  paramTypes: VType[],
  expectedRet?: VType,
): { binders: string[]; typed: string[]; body: Val; obligations: boolean; env: Env } {
  if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) fail(fn, "expected an inline arrow function `(x) => …`");
  let e2 = env;
  const binders: string[] = [];
  const typed: string[] = [];
  fn.parameters.forEach((p, i) => {
    const t = paramTypes[i];
    if (!t) fail(p, "unexpected extra lambda parameter");
    const r = bindParam(p.name, t, e2);
    e2 = r.env;
    binders.push(r.binder);
    typed.push(`(${r.binder} : ${leanType(t)})`);
  });
  const before = env.m.obCount();
  const body = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, e2, expectedRet, fn) : expr(fn.body, e2, expectedRet);
  return { binders, typed, body, obligations: env.m.obCount() > before, env: e2 };
}

/** Bind a parameter (identifier or object-destructuring pattern) to a fresh Lean variable. */
export function bindParam(name: ts.BindingName, t: VType, env: Env): { env: Env; binder: string } {
  if (ts.isIdentifier(name)) {
    const s = symbolOf(env, name)!;
    const { env: e2, name: ln } = freshLocal(env, leanIdent(name.text));
    return { env: bind(e2, s, { k: "val", code: ln, type: t }), binder: ln };
  }
  if (ts.isObjectBindingPattern(name)) {
    if (t.k !== "rec") fail(name, "destructuring is only supported for record types");
    const { env: e1, name: ln } = freshLocal(env, "o");
    let e2 = e1;
    const fields = env.m.reg.rec(t);
    for (const el of name.elements) {
      if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) fail(el, "only simple destructuring { a, b } is supported");
      const fname = el.propertyName ? el.propertyName.getText() : el.name.text;
      const f = fields.find((f) => f.name === fname);
      if (!f) fail(el, `no field ${fname}`);
      e2 = bind(e2, symbolOf(env, el.name)!, { k: "val", code: `${ln}.${leanField(fname)}`, type: f.type });
    }
    return { env: e2, binder: ln };
  }
  fail(name, "unsupported parameter pattern");
}

function call(c: ts.CallExpression, env: Env, expected?: VType): Val {
  const m = env.m;
  const callee = c.expression;
  const args = c.arguments;
  // vreact/spec helpers usable in expressions
  const sf = specFn(env, callee);
  if (sf) return specCall(sf, c, env);
  if (hookName(env, callee) && ts.isIdentifier(callee)) fail(c, `hook ${callee.text} must be called at the top level of a component (Rules of Hooks)`);
  // user pure function
  if (ts.isIdentifier(callee)) {
    const s = symbolOf(env, callee);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "closure") return inlineClosure(b, c, env, expected);
    if (b && b.k !== "val") fail(c, `\`${callee.text}\` can only be called as a statement inside an event handler or effect`);
    const g = globalOf(env, callee);
    if (g?.k === "fn") {
      const info = g.info;
      if (args.length !== info.params.length) fail(c, `${info.name} expects ${info.params.length} arguments`);
      if (env.curState && info.hasPre) {
        fail(c, `${info.name} has a precondition and cannot be called inside a functional update / reducer argument (its argument is the *current* state, about which nothing is known); make it total`);
      }
      const as = args.map((a, i) => paren(expr(a, env, info.params[i].type).code));
      const ob = info.hasPre ? " " + m.ob(c, "precondition", `precondition of ${info.name}(${args.map((a) => nodeText(a, 30)).join(", ")})`) : "";
      m.deps.add(info.qname);
      return { code: `(${info.qname}${as.map((a) => " " + a).join("")}${ob})`, type: info.ret };
    }
    if (callee.text === "String" && args.length === 1) return { code: toStr(expr(args[0], env), args[0]), type: T.str };
    fail(c, `call to \`${callee.text}\` is not supported (only verified top-level functions, local helper arrows, and modelled library methods)`);
  }
  if (ts.isPropertyAccessExpression(callee)) {
    const mname = callee.name.text;
    const objE = callee.expression;
    // Math.*
    if (ts.isIdentifier(objE) && objE.text === "Math") return mathCall(mname, c, env, expected);
    if (ts.isIdentifier(objE) && objE.text === "props") {
      const s = symbolOf(env, objE);
      if (s && env.vars.get(s)?.k === "props") fail(c, "callbacks can only be invoked as statements inside an event handler");
    }
    const obj = expr(objE, env);
    if (obj.type.k === "arr") return arrayMethod(mname, obj, c, env, expected);
    if (obj.type.k === "str") return stringMethod(mname, obj, c, env);
    if (obj.type.k === "opt") fail(c, `method call on a possibly-null value: narrow with !== null first`);
    fail(c, `method ${mname} not supported on ${showType(obj.type)}`);
  }
  fail(c, `unsupported call ${nodeText(c)}`);
}

function inlineClosure(b: Extract<Binding, { k: "closure" }>, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const fn = b.fn;
  if (fn.parameters.length !== c.arguments.length) fail(c, "arity mismatch");
  // Evaluate the arguments in the caller env, bind them in the closure's env.
  let lets = "";
  let e2: Env = { ...b.env, scope: env.scope, narrow: b.env.narrow, curState: env.curState };
  fn.parameters.forEach((p, i) => {
    if (!p.type) fail(p, "helper function parameters need type annotations");
    const t = typeOfNode(p.type, env.m.prog.typeEnv, "Arg");
    const a = expr(c.arguments[i], env, t);
    const r = bindParam(p.name, t, e2);
    e2 = r.env;
    lets += `let ${r.binder} := ${a.code}; `;
  });
  const retT = fn.type ? typeOfNode(fn.type, env.m.prog.typeEnv, "Ret") : expected;
  const body = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, e2, retT, fn) : expr(fn.body, e2, retT);
  return { code: lets ? `(${lets}${body.code})` : body.code, type: body.type };
}

function mathCall(name: string, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const args = c.arguments;
  const m = env.m;
  if ((name === "floor" || name === "trunc") && args.length === 1) {
    const inner = stripParens(args[0]);
    if (ts.isBinaryExpression(inner) && inner.operatorToken.kind === ts.SyntaxKind.SlashToken) {
      const l = expr(inner.left, env);
      const r = expr(inner.right, env);
      if (isIntLike(l.type) && isIntLike(r.type)) {
        const ob = m.ob(inner, "nonzero-divisor", `divisor ${nodeText(inner.right)} is non-zero`);
        return { code: `(VReact.JS.${name === "floor" ? "floorDiv" : "truncDiv"} ${paren(l.code)} ${paren(r.code)} ${ob})`, type: T.int };
      }
    }
    const v = expr(args[0], env);
    if (v.type.k === "int") return v;
    return { code: `(Float.${name === "floor" ? "floor" : "round"} ${paren(v.code)})`, type: T.num };
  }
  if ((name === "round" || name === "ceil") && args.length === 1) {
    const v = expr(args[0], env);
    if (v.type.k === "int") return v;
    return { code: name === "round" ? `(VReact.JS.mathRound ${paren(v.code)})` : `(Float.ceil ${paren(v.code)})`, type: T.num };
  }
  if ((name === "max" || name === "min") && args.length >= 2) {
    let vs = args.map((a) => expr(a, env, expected?.k === "num" ? T.num : undefined));
    const anyNum = vs.some((v) => v.type.k === "num");
    if (anyNum) vs = vs.map((v, i) => coerce(v, T.num, args[i], env));
    let code = vs[0].code;
    for (const v of vs.slice(1)) code = `(${name} ${paren(code)} ${paren(v.code)})`;
    return { code, type: anyNum ? T.num : T.int };
  }
  if (name === "abs" && args.length === 1) {
    const v = expr(args[0], env);
    return v.type.k === "int" ? { code: `(VReact.JS.abs ${paren(v.code)})`, type: T.int } : { code: `(Float.abs ${paren(v.code)})`, type: T.num };
  }
  if (name === "sign" && args.length === 1) {
    const v = expr(args[0], env, T.int);
    return { code: `(VReact.JS.sign ${paren(v.code)})`, type: T.int };
  }
  fail(c, `Math.${name} is not modelled in VTS`);
}

function lamCode(binders: string[], body: string): string {
  return `(fun ${binders.join(" ")} => ${body})`;
}

function arrayMethod(name: string, xs: Val, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const args = c.arguments;
  const m = env.m;
  const elem = (xs.type as { elem: VType }).elem;
  const X = paren(xs.code);
  const withAttach = (args0: ts.Expression, paramTypes: VType[], ret: VType | undefined) => {
    const lam = lambda(args0, env, paramTypes, ret);
    return lam;
  };
  switch (name) {
    case "map": {
      const fn = args[0];
      if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) fail(fn, "map needs an inline arrow function");
      if (fn.parameters.length === 2) {
        const lam = lambda(fn, env, [elem, T.int], expected?.k === "arr" ? expected.elem : undefined);
        if (lam.obligations) fail(fn, "map with an index parameter cannot contain proof obligations; precompute with a helper");
        const [x, i] = lam.binders;
        return { code: `(${X}.zipIdx.map (fun (${x}, ${i}0) => let ${i} : Int := ${i}0; ${lam.body.code}))`, type: T.arr(lam.body.type) };
      }
      const lam = withAttach(fn, [elem], expected?.k === "arr" ? expected.elem : undefined);
      if (lam.obligations) {
        const h = m.fresh("hmem");
        return { code: `(${X}.attach.map (fun ⟨${lam.binders[0]}, ${h}⟩ => ${lam.body.code}))`, type: T.arr(lam.body.type) };
      }
      return { code: `(${X}.map ${lamCode(lam.typed, lam.body.code)})`, type: T.arr(lam.body.type) };
    }
    case "filter":
    case "some":
    case "every":
    case "find": {
      const lam = withAttach(args[0], [elem], T.bool);
      const lean = { filter: "filter", some: "any", every: "all", find: "find?" }[name];
      const rt = name === "filter" ? xs.type : name === "find" ? T.opt(elem) : T.bool;
      if (lam.obligations) {
        const h = m.fresh("hmem");
        const core = `(${X}.attach.${lean} (fun ⟨${lam.binders[0]}, ${h}⟩ => ${lam.body.code}))`;
        if (name === "filter") return { code: `(${core}.map (·.1))`, type: rt };
        if (name === "find") return { code: `(${core}.map (·.1))`, type: rt };
        return { code: core, type: rt };
      }
      return { code: `(${X}.${lean} ${lamCode(lam.typed, lam.body.code)})`, type: rt };
    }
    case "findIndex": {
      const lam = lambda(args[0], env, [elem], T.bool);
      if (lam.obligations) fail(args[0], "findIndex predicates cannot contain proof obligations");
      return { code: `(VReact.JS.findIndex ${X} ${lamCode(lam.typed, lam.body.code)})`, type: T.int };
    }
    case "includes": {
      const v = expr(args[0], env, elem);
      return { code: `(${X}.contains ${paren(v.code)})`, type: T.bool };
    }
    case "indexOf": {
      const v = expr(args[0], env, elem);
      return { code: `(VReact.JS.indexOf ${X} ${paren(v.code)})`, type: T.int };
    }
    case "slice": {
      const a = args[0] ? expr(args[0], env, T.int).code : "0";
      const b = args[1] ? ` (some ${paren(expr(args[1], env, T.int).code)})` : "";
      return { code: `(VReact.JS.slice ${X} ${paren(a)}${b})`, type: xs.type };
    }
    case "concat": {
      const parts = args.map((a) => paren(expr(a, env, xs.type).code));
      return { code: `(${[X, ...parts].join(" ++ ")})`, type: xs.type };
    }
    case "join": {
      if (elem.k !== "str") fail(c, "join is supported on string arrays (map to strings first)");
      const sep = args[0] ? expr(args[0], env, T.str).code : jsStr(",");
      return { code: `(VReact.JS.join ${X} ${paren(sep)})`, type: T.str };
    }
    case "reduce": {
      if (args.length !== 2) fail(c, "reduce needs an initial value");
      const init = expr(args[1], env, expected);
      const lam = lambda(args[0], env, [init.type, elem], init.type);
      if (lam.obligations) fail(args[0], "reduce callbacks cannot contain proof obligations");
      return { code: `(${X}.foldl ${lamCode(lam.typed, lam.body.code)} ${paren(init.code)})`, type: init.type };
    }
    case "toSorted": {
      if (!args[0]) fail(c, "toSorted needs a comparator (a, b) => number");
      if (elem.k === "opt" && ts.isPropertyAccessExpression(c.expression)) {
        // JS moves `undefined` elements to the end without calling the comparator
        const at = env.m.checker.getTypeAtLocation(c.expression.expression);
        const et = env.m.checker.getIndexTypeOfType(at, ts.IndexKind.Number);
        const undef = (t: ts.Type) => !!(t.flags & ts.TypeFlags.Undefined);
        if (!et || undef(et) || (et.isUnion() && et.types.some(undef)))
          fail(c, "toSorted on an array that may contain undefined is not supported (JS sorts undefined to the end without calling the comparator); filter or map the elements to a defined type first");
      }
      const lam = lambda(args[0], env, [elem, elem], T.int);
      if (lam.obligations) fail(args[0], "comparators cannot contain proof obligations");
      if (lam.body.type.k !== "int") fail(args[0], "comparator must return an int");
      return { code: `(VReact.JS.toSorted ${X} ${lamCode(lam.typed, lam.body.code)})`, type: xs.type };
    }
    case "toReversed":
      return { code: `(${X}.reverse)`, type: xs.type };
    case "with": {
      const i = expr(args[0], env, T.int);
      const v = expr(args[1], env, elem);
      const ob = m.ob(c, "index", `index ${nodeText(args[0])} is within bounds for .with`);
      return { code: `(VReact.JS.withAt ${X} ${paren(i.code)} ${paren(v.code)} ${ob})`, type: xs.type };
    }
    case "at": {
      const i = expr(args[0], env, T.int);
      return { code: `(VReact.JS.atOpt ${X} ${paren(i.code)})`, type: T.opt(elem) };
    }
    case "flatMap": {
      const lam = lambda(args[0], env, [elem], expected);
      if (lam.obligations) fail(args[0], "flatMap callbacks cannot contain proof obligations");
      if (lam.body.type.k !== "arr") fail(args[0], "flatMap callback must return an array");
      return { code: `(${X}.flatMap ${lamCode(lam.typed, lam.body.code)})`, type: lam.body.type };
    }
    case "push":
    case "pop":
    case "shift":
    case "unshift":
    case "splice":
    case "sort":
    case "reverse":
    case "fill":
    case "copyWithin":
      fail(c, `${name} mutates the array; VTS data is immutable (use spread, filter, toSorted, toReversed, with)`);
    default:
      fail(c, `array method ${name} is not modelled in VTS`);
  }
}

function stringMethod(name: string, s: Val, c: ts.CallExpression, env: Env): Val {
  const args = c.arguments;
  const S = paren(s.code);
  switch (name) {
    case "trim":
      return { code: `(VReact.JS.trim ${S})`, type: T.str };
    case "toLowerCase":
      return { code: `(VReact.JS.toLowerCase ${S})`, type: T.str };
    case "toUpperCase":
      return { code: `(VReact.JS.toUpperCase ${S})`, type: T.str };
    case "includes":
      return { code: `(VReact.JS.strIncludes ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "startsWith":
      return { code: `(VReact.JS.startsWith ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "endsWith":
      return { code: `(VReact.JS.endsWith ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "slice": {
      const a = args[0] ? expr(args[0], env, T.int).code : "0";
      const b = args[1] ? ` (some ${paren(expr(args[1], env, T.int).code)})` : "";
      return { code: `(VReact.JS.strSlice ${S} ${paren(a)}${b})`, type: T.str };
    }
    case "repeat": {
      const n = expr(args[0], env, T.int);
      const ob = env.m.ob(c, "precondition", `repeat count ${nodeText(args[0])} is non-negative`);
      return { code: `(VReact.JS.strRepeat ${S} ${paren(n.code)} ${ob})`, type: T.str };
    }
    default:
      fail(c, `string method ${name} is not modelled in VTS`);
  }
}

/** vreact/spec functions in expression position. */
function specCall(name: string, c: ts.CallExpression, env: Env): Val {
  const args = c.arguments;
  switch (name) {
    case "forall":
    case "exists": {
      const lo = expr(args[0], env, T.int);
      const hi = expr(args[1], env, T.int);
      const lam = lambda(args[2], env, [T.int], T.bool);
      const op = name === "forall" ? "all" : "any";
      return { code: `((VReact.JS.rangeFrom ${paren(lo.code)} ${paren(hi.code)}).${op} ${lamCode(lam.typed, lam.body.code)})`, type: T.bool };
    }
    case "distinct": {
      const xs = expr(args[0], env);
      if (xs.type.k !== "arr") fail(c, "distinct expects an array");
      if (args[1]) {
        const lam = lambda(args[1], env, [xs.type.elem]);
        return { code: `(VReact.JS.nodupB (${paren(xs.code)}.map ${lamCode(lam.typed, lam.body.code)}))`, type: T.bool };
      }
      return { code: `(VReact.JS.nodupB ${paren(xs.code)})`, type: T.bool };
    }
    case "implies": {
      const a = expr(args[0], env, T.bool);
      const b = expr(args[1], env, T.bool);
      return { code: `((!${paren(a.code)}) || ${paren(b.code)})`, type: T.bool };
    }
    case "idiv": {
      const a = expr(args[0], env, T.int);
      const b = expr(args[1], env, T.int);
      const ob = env.m.ob(c, "nonzero-divisor", `divisor ${nodeText(args[1])} is non-zero`);
      return { code: `(VReact.JS.floorDiv ${paren(a.code)} ${paren(b.code)} ${ob})`, type: T.int };
    }
    case "range": {
      const n = expr(args[0], env, T.int);
      return { code: `(VReact.JS.range ${paren(n.code)})`, type: T.arr(T.int) };
    }
    case "hole": {
      // an unfilled synthesis placeholder: translated as `sorry` (reported INCOMPLETE)
      const t = c.typeArguments?.[0] ? typeOfNode(c.typeArguments[0], env.m.prog.typeEnv, "Hole") : undefined;
      if (!t) fail(c, "write hole<T>() with an explicit type");
      return { code: `(sorry : ${leanType(t)})`, type: t };
    }
    default:
      fail(c, `${name}(…) is a statement-level contract, not an expression`);
  }
}

/* ─────────────────────── conditions & narrowing ─────────────────────── */

function hasNarrowing(e: ts.Expression, env: Env): boolean {
  e = stripParens(e);
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) return hasNarrowing(e.operand, env);
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (k === ts.SyntaxKind.AmpersandAmpersandToken || k === ts.SyntaxKind.BarBarToken) return hasNarrowing(e.left, env) || hasNarrowing(e.right, env);
  }
  return narrowTest(e, env) !== null;
}

interface NarrowTest {
  kind: "null" | "tag";
  target: ts.Expression;
  /** true if the test succeeds when the value is null / matches the variant */
  positive: boolean;
  variant?: string;
}

function narrowTest(e: ts.Expression, env: Env): NarrowTest | null {
  e = stripParens(e);
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (!(isEqOp(k) || isNeqOp(k))) return null;
    const neg = isNeqOp(k);
    if (isNullLit(e.right) || isNullLit(e.left)) {
      const target = isNullLit(e.right) ? e.left : e.right;
      if (!pathKey(env, target)) return null;
      return { kind: "null", target, positive: !neg };
    }
    // x.kind === "lit"
    const tryTag = (acc: ts.Expression, lit: ts.Expression): NarrowTest | null => {
      if (!ts.isPropertyAccessExpression(acc) || !ts.isStringLiteralLike(lit)) return null;
      if (!pathKey(env, acc.expression)) return null;
      let t: VType;
      try {
        t = expr(acc.expression, { ...env, m: dryCtx(env.m) }).type;
      } catch {
        return null;
      }
      if (t.k !== "union") return null;
      const u = env.m.reg.union(t);
      if (acc.name.text !== u.tag) return null;
      return { kind: "tag", target: acc.expression, positive: !neg, variant: lit.text };
    };
    return tryTag(e.left, e.right) ?? tryTag(e.right, e.left);
  }
  return null;
}

/** A throw-away module context for type queries (obligations are discarded). */
function dryCtx(m: ModCtx): ModCtx {
  const d = Object.create(m) as ModCtx;
  d.obligations = [];
  d.counter = { n: 0 };
  d.ob = () => "(by sorry)";
  d.obCount = () => 0;
  return d;
}

/** Typecheck an expression without emitting obligations. */
export function typeOf(e: ts.Expression, env: Env, expected?: VType): VType {
  return expr(e, { ...env, m: dryCtx(env.m) }, expected).type;
}

/**
 * Compile a boolean condition into a branching Lean term.  `onTrue`/`onFalse`
 * build the branches in environments refined by the condition (narrowing).
 */
export function branch(c: ts.Expression, env: Env, onTrue: (e: Env) => string, onFalse: (e: Env) => string): string {
  const e = stripParens(c);
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) return branch(e.operand, env, onFalse, onTrue);
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) {
    return branch(e.left, env, (e1) => branch(e.right, e1, onTrue, onFalse), onFalse);
  }
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.BarBarToken) {
    return branch(e.left, env, onTrue, (e2) => branch(e.right, e2, onTrue, onFalse));
  }
  const nt = narrowTest(e, env);
  if (nt) return narrowBranch(nt, env, onTrue, onFalse);
  // truthiness of an optional object/array
  const key = pathKey(env, e);
  if (key) {
    let t: VType | null = null;
    try {
      t = typeOf(e, env);
    } catch {
      t = null;
    }
    if (t?.k === "opt") {
      if (["rec", "arr", "union", "tuple"].includes(t.elem.k)) {
        return narrowBranch({ kind: "null", target: e, positive: false }, env, onTrue, onFalse);
      }
      fail(c, `truthiness of ${showType(t)} is ambiguous (0, "" and false are falsy): compare with null explicitly`);
    }
  }
  const v = expr(e, env, T.bool);
  const h = env.m.fresh("h");
  const t = onTrue(env);
  const f = onFalse(env);
  if (t === "true" && f === "false") return paren(v.code);
  if (t === "false" && f === "true") return `(!${paren(v.code)})`;
  return `(if ${h} : ${paren(v.code)} = true then ${paren(t)} else ${paren(f)})`;
}

function narrowBranch(nt: NarrowTest, env: Env, onTrue: (e: Env) => string, onFalse: (e: Env) => string): string {
  const target = expr(nt.target, env);
  const key = pathKey(env, nt.target)!;
  const h = env.m.fresh("h");
  if (nt.kind === "null") {
    if (target.type.k !== "opt") fail(nt.target, "null test on a non-optional value");
    const base = ts.isIdentifier(nt.target) ? leanIdent(nt.target.text) : ts.isPropertyAccessExpression(nt.target) ? leanIdent(nt.target.name.text) : "v";
    const { env: e1, name: v } = freshLocal(env, base);
    const narrow = new Map(e1.narrow);
    narrow.set(key, { kind: "some", code: v, type: target.type.elem });
    const someEnv = { ...e1, narrow };
    const whenNull = nt.positive ? onTrue : onFalse;
    const whenSome = nt.positive ? onFalse : onTrue;
    return `(match ${h} : ${target.code} with\n  | some ${v} => ${paren(whenSome(someEnv))}\n  | none => ${paren(whenNull(env))})`;
  }
  // tag test
  if (target.type.k !== "union") fail(nt.target, "discriminant test on a non-union");
  const u = env.m.reg.union(target.type);
  const variant = u.variants.find((v) => v.lit === nt.variant);
  if (!variant) fail(nt.target, `"${nt.variant}" is not a variant of ${showType(target.type)}`);
  let e1 = env;
  const names: string[] = [];
  const fields = new Map<string, Val>();
  for (const f of variant.fields) {
    const r = freshLocal(e1, leanIdent(f.name));
    e1 = r.env;
    names.push(r.name);
    fields.set(f.name, { code: r.name, type: f.type });
  }
  const narrow = new Map(e1.narrow);
  narrow.set(key, { kind: "variant", code: target.code, type: target.type, variant: variant.lit, fields });
  const inEnv = { ...e1, narrow };
  const yes = nt.positive ? onTrue(inEnv) : onFalse(inEnv);
  const others = u.variants.length > 1;
  const no = others ? (nt.positive ? onFalse(env) : onTrue(env)) : null;
  const pat = `.${leanField(variant.ctor)}${names.map((n) => " " + n).join("")}`;
  return `(match ${h} : ${target.code} with\n  | ${pat} => ${paren(yes)}${no !== null ? `\n  | _ => ${paren(no)}` : ""})`;
}

/**
 * A VTS boolean expression as a Lean proposition (used for contracts:
 * requires / invariant / ensures / callbackRequires / assert).  Connectives,
 * comparisons and quantifying array methods become logical connectives and
 * quantifiers, so that automation never sees `decide` instances in specs.
 */
export function prop(e0: ts.Expression, env: Env): string {
  const e = stripParens(e0);
  const K = ts.SyntaxKind;
  if (e.kind === K.TrueKeyword) return "True";
  if (e.kind === K.FalseKeyword) return "False";
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.ExclamationToken) {
    const nt = narrowTest(e.operand, env);
    if (nt) return propNarrow({ ...nt, positive: !nt.positive }, env, () => "True", () => "False");
    return `¬${paren(prop(e.operand, env))}`;
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.kind;
    if (op === K.AmpersandAmpersandToken) {
      const nt = narrowTest(e.left, env);
      if (nt) return propNarrow(nt, env, (e1) => prop(e.right, e1), () => "False");
      return `(${prop(e.left, env)} ∧ ${prop(e.right, env)})`;
    }
    if (op === K.BarBarToken) {
      const nt = narrowTest(e.left, env);
      if (nt) return propNarrow(nt, env, () => "True", (e2) => prop(e.right, e2));
      return `(${prop(e.left, env)} ∨ ${prop(e.right, env)})`;
    }
    const nt = narrowTest(e, env);
    if (nt) return propNarrow(nt, env, () => "True", () => "False");
    if (isEqOp(op) || isNeqOp(op)) {
      let l = expr(e.left, env);
      let r = expr(e.right, env, l.type.k === "enum" || l.type.k === "opt" ? l.type : undefined);
      if (l.type.k === "str" && r.type.k === "enum") l = expr(e.left, env, r.type);
      if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, e, env);
      if (r.type.k === "int" && l.type.k === "num") r = coerce(r, T.num, e, env);
      if (["rec", "arr", "union", "tuple"].includes(l.type.k)) fail(e, `=== on ${showType(l.type)} compares object identity in JS; compare keys/fields instead`);
      return `(${l.code} ${isNeqOp(op) ? "≠" : "="} ${r.code})`;
    }
    const cmp: Record<number, string> = { [K.LessThanToken]: "<", [K.LessThanEqualsToken]: "≤", [K.GreaterThanToken]: ">", [K.GreaterThanEqualsToken]: "≥" };
    if (cmp[op]) {
      let l = expr(e.left, env);
      let r = expr(e.right, env, l.type);
      if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, e, env);
      if (!isNumeric(l.type)) fail(e, "ordering comparison on non-numbers");
      return `(${l.code} ${cmp[op]} ${r.code})`;
    }
  }
  if (ts.isConditionalExpression(e)) {
    const c = prop(e.condition, env);
    return `((${c} → ${prop(e.whenTrue, env)}) ∧ (¬${paren(c)} → ${prop(e.whenFalse, env)}))`;
  }
  if (ts.isCallExpression(e)) {
    const sf = specFn(env, e.expression);
    const args = e.arguments;
    if (sf === "implies") return `(${prop(args[0], env)} → ${prop(args[1], env)})`;
    if (sf === "forall" || sf === "exists") {
      const lo = expr(args[0], env, T.int);
      const hi = expr(args[1], env, T.int);
      const fn = args[2];
      if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length !== 1) fail(e, `${sf}(lo, hi, (i) => …)`);
      const r = bindParam(fn.parameters[0].name, T.int, env);
      if (ts.isBlock(fn.body)) fail(fn.body, "quantifier body must be an expression");
      const body = prop(fn.body, r.env);
      return sf === "forall"
        ? `(∀ ${r.binder} : Int, ${paren(lo.code)} ≤ ${r.binder} → ${r.binder} < ${paren(hi.code)} → ${body})`
        : `(∃ ${r.binder} : Int, ${paren(lo.code)} ≤ ${r.binder} ∧ ${r.binder} < ${paren(hi.code)} ∧ ${body})`;
    }
    if (sf === "distinct") {
      const xs = expr(args[0], env);
      if (xs.type.k !== "arr") fail(e, "distinct expects an array");
      if (!args[1]) return `(${paren(xs.code)}.Nodup)`;
      const lam = lambda(args[1], env, [xs.type.elem]);
      return `((${paren(xs.code)}.map ${lamCode(lam.typed, lam.body.code)}).Nodup)`;
    }
    if (ts.isPropertyAccessExpression(e.expression) && ["every", "some", "includes"].includes(e.expression.name.text)) {
      const xs = expr(e.expression.expression, env);
      if (xs.type.k === "arr") {
        const mname = e.expression.name.text;
        if (mname === "includes") return `(${expr(args[0], env, xs.type.elem).code} ∈ ${paren(xs.code)})`;
        const fn = args[0];
        if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length !== 1 || ts.isBlock(fn.body)) {
          fail(e, `${mname}((x) => condition) with an expression body`);
        }
        const r = bindParam(fn.parameters[0].name, xs.type.elem, env);
        const body = prop(fn.body as ts.Expression, r.env);
        return mname === "every" ? `(∀ ${r.binder} ∈ ${paren(xs.code)}, ${body})` : `(∃ ${r.binder} ∈ ${paren(xs.code)}, ${body})`;
      }
    }
  }
  const v = expr(e, env, T.bool);
  return `(${paren(v.code)} = true)`;
}

/** Narrowing inside propositions: `x !== null && P(x)` ↦ `match x with | some x => P x | none => False`. */
function propNarrow(nt: NarrowTest, env: Env, onTrue: (e: Env) => string, onFalse: (e: Env) => string): string {
  const s = narrowBranch(nt, env, onTrue, onFalse);
  // narrowBranch names the equation hypothesis `h_N : …`; drop it inside propositions
  return s.replace(/^\(match h_\d+ : /, "(match ");
}

/* ───────────────────────────── statements ───────────────────────────── */

export type Kind = "value" | "handler" | "render";

export interface BlockCtx {
  kind: Kind;
  /** expected return type (value blocks) */
  ret?: VType;
  /** render: produces the final VNode for a returned JSX expression */
  onReturn?: (e: ts.Expression | undefined, env: Env) => string;
  /** handler: produce the outcome term */
  onDone?: (env: Env) => string;
  fnNode: ts.Node;
}

/** A value-returning block (function bodies, block-bodied lambdas). */
export function valueBlock(stmts: readonly ts.Statement[], env: Env, ret: VType | undefined, fnNode: ts.Node): Val {
  let rt = ret;
  const bc: BlockCtx = {
    kind: "value",
    ret,
    fnNode,
    onReturn: (e, env2) => {
      if (!e) fail(fnNode, "missing return value");
      const v = expr(e, env2, rt);
      rt = rt ?? v.type;
      return v.code;
    },
  };
  const code = block(stmts, 0, env, bc, () => fail(fnNode, "function may finish without returning a value"));
  return { code, type: rt ?? T.void };
}

export function block(stmts: readonly ts.Statement[], i: number, env: Env, bc: BlockCtx, k: (env: Env) => string): string {
  if (i >= stmts.length) return k(env);
  const s = stmts[i];
  const rest = (e2: Env) => block(stmts, i + 1, e2, bc, k);
  const m = env.m;
  if (ts.isVariableStatement(s)) {
    const isConst = (s.declarationList.flags & ts.NodeFlags.Const) !== 0;
    const isLet = (s.declarationList.flags & ts.NodeFlags.Let) !== 0;
    if (!isConst && !isLet) fail(s, "use const or let (no var)");
    return varDecls(s.declarationList.declarations, 0, env, bc, rest);
  }
  if (ts.isExpressionStatement(s)) return exprStatement(s.expression, env, bc, rest);
  if (ts.isIfStatement(s)) {
    const els = s.elseStatement;
    return branch(
      s.expression,
      env,
      (e1) => block(blockOf(s.thenStatement), 0, e1, bc, rest),
      (e2) => (els ? block(blockOf(els), 0, e2, bc, rest) : rest(e2)),
    );
  }
  if (ts.isBlock(s)) return block(s.statements, 0, env, bc, rest);
  if (ts.isReturnStatement(s)) {
    if (i !== stmts.length - 1) {
      // unreachable code after return
      fail(stmts[i + 1], "unreachable code after return");
    }
    if (bc.kind === "handler") {
      if (s.expression) fail(s, "event handlers return nothing");
      return bc.onDone!(env);
    }
    return bc.onReturn!(s.expression, env);
  }
  if (ts.isSwitchStatement(s)) return switchStmt(s, env, bc, rest);
  if (ts.isForOfStatement(s)) return forOf(s, env, bc, rest);
  if (ts.isThrowStatement(s)) {
    const ob = m.ob(s, "unreachable", `this throw is unreachable`);
    return `(False.elim ${ob})`;
  }
  if (ts.isEmptyStatement(s)) return rest(env);
  if (ts.isFunctionDeclaration(s)) fail(s, "nested function declarations are not supported: use a const arrow function");
  if (ts.isWhileStatement(s) || ts.isDoStatement(s) || ts.isForStatement(s) || ts.isForInStatement(s)) {
    fail(s, "only `for (const x of xs)` loops are supported in VTS (they always terminate); use array methods or for…of");
  }
  if (ts.isTryStatement(s)) fail(s, "try/catch is not supported: VTS code is exception-free by construction");
  fail(s, `statement not supported in VTS: ${nodeText(s)}`);
}

function blockOf(s: ts.Statement): readonly ts.Statement[] {
  return ts.isBlock(s) ? s.statements : [s];
}

function varDecls(decls: ts.NodeArray<ts.VariableDeclaration>, j: number, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  if (j >= decls.length) return rest(env);
  const d = decls[j];
  const next = (e2: Env) => varDecls(decls, j + 1, e2, bc, rest);
  if (!d.initializer) fail(d, "variables must be initialised");
  const init = stripParens(d.initializer);
  const declT = d.type ? typeOfNode(d.type, env.m.prog.typeEnv, ts.isIdentifier(d.name) ? capitalize(d.name.text) : "Local") : undefined;
  // local arrow function: a closure (inlined at use sites)
  if ((ts.isArrowFunction(init) || ts.isFunctionExpression(init)) && ts.isIdentifier(d.name)) {
    return next(bind(env, symbolOf(env, d.name)!, { k: "closure", fn: init, env }));
  }
  // useCallback(fn, deps) is a closure too (exhaustive deps make it equivalent to a fresh closure)
  if (ts.isCallExpression(init) && hookName(env, init.expression) === "useCallback" && ts.isIdentifier(d.name)) {
    const fn = init.arguments[0];
    if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) fail(init, "useCallback needs an inline function");
    checkDeps(fn, init.arguments[1], env, "useCallback");
    return next(bind(env, symbolOf(env, d.name)!, { k: "closure", fn, env }));
  }
  if (ts.isCallExpression(init) && hookName(env, init.expression) === "useMemo" && ts.isIdentifier(d.name)) {
    const fn = init.arguments[0];
    if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length) fail(init, "useMemo needs an inline () => value");
    checkDeps(fn, init.arguments[1], env, "useMemo");
    const v = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, env, declT, fn) : expr(fn.body, env, declT);
    return bindLocal(d.name, v, env, next);
  }
  if (ts.isCallExpression(init) && hookName(env, init.expression)) {
    fail(init, `hooks must be called at the top level of a component, unconditionally (Rules of Hooks)`);
  }
  // JSX-valued const (inlined where used)
  if (ts.isJsxElement(init) || ts.isJsxSelfClosingElement(init) || ts.isJsxFragment(init)) {
    if (!ts.isIdentifier(d.name)) fail(d, "destructuring JSX");
    return next(bind(env, symbolOf(env, d.name)!, { k: "jsx", node: init, env }));
  }
  if (ts.isObjectBindingPattern(d.name)) {
    const v = expr(init, env, declT);
    const { env: e1, name: tmp } = freshLocal(env, "tmp");
    const r = bindParam(d.name, v.type, e1);
    // bindParam created its own local name; re-bind to tmp
    return `(let ${r.binder} := ${v.code};\n${next(r.env)})`;
  }
  if (!ts.isIdentifier(d.name)) fail(d, "unsupported destructuring");
  const v = expr(init, env, declT);
  return bindLocal(d.name, v, env, next);
}

function bindLocal(name: ts.BindingName, v: Val, env: Env, next: (e: Env) => string): string {
  if (!ts.isIdentifier(name)) fail(name, "unsupported binding");
  const s = symbolOf(env, name)!;
  const { env: e1, name: ln } = freshLocal(env, leanIdent(name.text));
  const e2 = bind(e1, s, { k: "val", code: ln, type: v.type });
  return `(let ${ln} := ${v.code};\n${next(e2)})`;
}

/** Re-bind a mutable local after assignment. */
function assignLocal(target: ts.Expression, newVal: (old: Val) => Val, env: Env, next: (e: Env) => string, node: ts.Node): string {
  if (!ts.isIdentifier(target)) fail(node, "only local `let` variables can be assigned (VTS data is immutable)");
  const s = symbolOf(env, target);
  const b = s ? env.vars.get(s) : undefined;
  if (!b || b.k !== "val") fail(node, `cannot assign to ${target.text}`);
  const decl = s!.valueDeclaration;
  if (!decl || !ts.isVariableDeclaration(decl) || !(decl.parent.flags & ts.NodeFlags.Let)) fail(node, `${target.text} is not a local let variable`);
  const v = newVal({ code: b.code, type: b.type });
  const c = coerce(v, b.type, node, env);
  const { env: e1, name: ln } = freshLocal(env, leanIdent(target.text));
  return `(let ${ln} := ${c.code};\n${next(bind(e1, s!, { k: "val", code: ln, type: b.type }))})`;
}

function exprStatement(e: ts.Expression, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  const m = env.m;
  e = stripParens(e);
  // assignments
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (k === ts.SyntaxKind.EqualsToken) {
      if (ts.isPropertyAccessExpression(e.left) && e.left.getText() === "document.title") return rest(env); // external effect
      return assignLocal(e.left, (old) => expr(e.right, env, old.type), env, rest, e);
    }
    if (k === ts.SyntaxKind.PlusEqualsToken || k === ts.SyntaxKind.MinusEqualsToken) {
      const op = k === ts.SyntaxKind.PlusEqualsToken ? "+" : "-";
      return assignLocal(e.left, (old) => {
        const r = expr(e.right, env, old.type);
        if (old.type.k === "str" && op === "+") return { code: `(${old.code} ++ ${toStr(r, e.right)})`, type: T.str };
        return arith(op, old, r, e, env);
      }, env, rest, e);
    }
  }
  if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
    const op = e.operator === ts.SyntaxKind.PlusPlusToken ? "+" : "-";
    return assignLocal(e.operand, (old) => ({ code: `(${old.code} ${op} 1)`, type: old.type }), env, rest, e);
  }
  if (!ts.isCallExpression(e)) fail(e, "expression statement has no effect");
  const callee = e.expression;
  const sf = specFn(env, callee);
  if (sf) {
    switch (sf) {
      case "assert": {
        const p = prop(e.arguments[0], env);
        const h = m.fresh("hassert");
        const ob = m.ob(e, "assert", `assertion ${nodeText(e.arguments[0])}`);
        return `(have ${h} : ${p} := ${ob};\n${rest(env)})`;
      }
      case "assume": {
        const p = prop(e.arguments[0], env);
        const h = m.fresh("hassume");
        return `(have ${h} : ${p} := VReact.assumed;\n${rest(env)})`;
      }
      case "requires":
      case "ensures":
      case "invariant":
      case "callbackRequires":
      case "decreases":
        fail(e, `${sf}(…) must appear at the start of a function/component body`);
      default:
        fail(e, `${sf}(…) has no effect as a statement`);
    }
  }
  // console.*, e.preventDefault(), localStorage writes: external, no effect on component state
  if (ts.isPropertyAccessExpression(callee)) {
    const objText = callee.expression.getText();
    if (objText === "console") return rest(env);
    if (objText === "localStorage" && callee.name.text === "setItem") return rest(env);
    if (["preventDefault", "stopPropagation"].includes(callee.name.text) && ts.isIdentifier(callee.expression)) {
      const s = symbolOf(env, callee.expression);
      if (s && env.vars.get(s)?.k === "event") return rest(env);
    }
  }
  // state updates / callbacks: only in handlers
  const target = updateTarget(callee, env);
  if (target) {
    if (bc.kind !== "handler" || !env.handler) {
      fail(e, target.k === "callback"
        ? "a parent callback can only be invoked inside an event handler"
        : "state updates during render are not allowed (setState in render causes re-render loops); move it into an event handler or effect");
    }
    return handlerEffect(target, e, env, rest);
  }
  // calling a local closure as a statement inside a handler: inline its statements
  if (ts.isIdentifier(callee)) {
    const s = symbolOf(env, callee);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "closure" && bc.kind === "handler") {
      const fn = b.fn;
      let e2: Env = { ...b.env, handler: env.handler, scope: env.scope, curState: undefined };
      let lets = "";
      fn.parameters.forEach((p, i) => {
        if (!p.type) fail(p, "helper parameters need type annotations");
        const t = typeOfNode(p.type, m.prog.typeEnv, "Arg");
        const a = expr(e.arguments[i], env, t);
        const r = bindParam(p.name, t, e2);
        e2 = r.env;
        lets += `let ${r.binder} := ${a.code};\n`;
      });
      const stmts = ts.isBlock(fn.body) ? fn.body.statements : [ts.factory.createExpressionStatement(fn.body)];
      if (!ts.isBlock(fn.body)) {
        // expression-bodied: treat as a single statement
        return lets + exprStatement(fn.body, e2, bc, (e3) => rest({ ...env, handler: e3.handler, scope: e3.scope }));
      }
      const inner: BlockCtx = { ...bc, onDone: (e3) => rest({ ...env, handler: e3.handler, scope: e3.scope }) };
      return `(${lets}${block(stmts, 0, e2, inner, (e3) => rest({ ...env, handler: e3.handler, scope: e3.scope }))})`;
    }
  }
  if (ts.isPropertyAccessExpression(callee) && ["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin", "set", "delete", "add", "clear"].includes(callee.name.text)) {
    fail(e, `${callee.name.text} mutates the array/object; VTS data is immutable (use spread, filter, toSorted, toReversed, with)`);
  }
  if (ts.isCallExpression(e) && hookName(env, callee)) fail(e, "hooks must be called at the top level of a component, unconditionally (Rules of Hooks)");
  fail(e, `this call has no modelled effect: ${nodeText(e)}`);
}

type UpdTarget =
  | { k: "setter"; sv: StateVar }
  | { k: "dispatch"; sv: StateVar }
  | { k: "callback"; name: string };

function updateTarget(callee: ts.Expression, env: Env): UpdTarget | null {
  if (ts.isIdentifier(callee)) {
    const s = symbolOf(env, callee);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "setter") return { k: "setter", sv: b.sv };
    if (b?.k === "dispatch") return { k: "dispatch", sv: b.sv };
    if (b?.k === "callback") return { k: "callback", name: b.cb.name };
  }
  if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression)) {
    const s = symbolOf(env, callee.expression);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "props") {
      const cb = env.comp!.info.callbacks.find((c) => c.name === callee.name.text);
      if (cb) return { k: "callback", name: cb.name };
    }
  }
  return null;
}

/** A setter / dispatch / callback call inside a handler. */
function handlerEffect(t: UpdTarget, c: ts.CallExpression, env: Env, rest: (e: Env) => string): string {
  const m = env.m;
  const h = env.handler!;
  const comp = env.comp!;
  if (t.k === "setter") {
    const sv = t.sv;
    const arg = c.arguments[0];
    if (!arg) fail(c, "setter needs an argument");
    const a = stripParens(arg);
    let upd: string;
    if (ts.isArrowFunction(a) || ts.isFunctionExpression(a)) {
      // functional update: argument is the *current* state at application time
      if (a.parameters.length !== 1) fail(a, "functional updates take one parameter");
      const tau = "τ";
      const r = bindParam(a.parameters[0].name, sv.type, { ...env, curState: tau });
      const e2 = { ...r.env, curState: tau };
      const body = ts.isBlock(a.body) ? valueBlock(a.body.statements, e2, sv.type, a) : expr(a.body, e2, sv.type);
      upd = `(fun ${tau} => { ${tau} with ${leanField(sv.field)} := (let ${r.binder} := ${tau}.${leanField(sv.field)}; ${body.code}) })`;
    } else {
      const v = expr(a, env, sv.type);
      upd = `(fun τ => { τ with ${leanField(sv.field)} := ${paren(v.code)} })`;
    }
    return rest({ ...env, handler: { ...h, updates: [...h.updates, upd] } });
  }
  if (t.k === "dispatch") {
    const sv = t.sv;
    const a = expr(c.arguments[0], env, sv.actionType);
    m.deps.add(sv.reducer!.qname);
    const upd = `(fun τ => { τ with ${leanField(sv.field)} := ${sv.reducer!.qname} τ.${leanField(sv.field)} ${paren(a.code)} })`;
    return rest({ ...env, handler: { ...h, updates: [...h.updates, upd] } });
  }
  // callback
  if (h.kind === "robust") fail(c, "parent callbacks cannot be invoked from effects, timers or continuous events (their snapshot may be stale)");
  if (h.emit) fail(c, "a handler may invoke at most one parent callback per execution path (otherwise the parent's updates would not be checked together)");
  const cb = comp.info.callbacks.find((x) => x.name === t.name)!;
  if (c.arguments.length !== cb.params.length) fail(c, `${cb.name} expects ${cb.params.length} arguments`);
  const as = c.arguments.map((a, i) => paren(expr(a, env, cb.params[i].type).code));
  const ob = m.ob(c, "callback-contract", `callback contract of ${cb.name}(${c.arguments.map((a) => nodeText(a, 30)).join(", ")})`);
  const emit = `(${comp.cbVar}.${leanField(cb.name)}${as.map((a) => " " + a).join("")} ${ob})`;
  return rest({ ...env, handler: { ...h, emit } });
}

function switchStmt(s: ts.SwitchStatement, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  const disc = stripParens(s.expression);
  const m = env.m;
  // collect clauses: groups of case labels sharing a body
  interface Group {
    labels: string[];
    body: ts.Statement[];
    isDefault: boolean;
    node: ts.Node;
  }
  const groups: Group[] = [];
  let pending: string[] = [];
  for (const cl of s.caseBlock.clauses) {
    if (ts.isCaseClause(cl)) {
      const lit = stripParens(cl.expression);
      if (!ts.isStringLiteralLike(lit) && !ts.isNumericLiteral(lit)) fail(cl.expression, "case labels must be literals");
      pending.push(lit.text);
    }
    if (cl.statements.length === 0) continue;
    const body = [...cl.statements];
    const last = body[body.length - 1];
    const endsWithBreak = ts.isBreakStatement(last);
    if (endsWithBreak) body.pop();
    else if (!terminates(body)) fail(cl, "switch cases must end with break, return or throw (no fall-through)");
    groups.push({ labels: pending, body, isDefault: ts.isDefaultClause(cl), node: cl });
    pending = [];
  }
  const after = (e2: Env) => rest(e2);
  // discriminated union switch: switch (a.kind)
  if (ts.isPropertyAccessExpression(disc)) {
    const baseT = typeOf(disc.expression, env);
    if (baseT.k === "union" && m.reg.union(baseT).tag === disc.name.text) {
      const u = m.reg.union(baseT);
      const target = expr(disc.expression, env);
      const key = pathKey(env, disc.expression);
      const h = m.fresh("h");
      const covered = new Set<string>();
      let arms = "";
      let hasDefault = false;
      for (const g of groups) {
        if (g.isDefault && g.labels.length === 0) {
          hasDefault = true;
          arms += `\n  | _ => ${paren(block(g.body, 0, env, bc, after))}`;
          continue;
        }
        for (const l of g.labels) if (!u.variants.some((v) => v.lit === l)) fail(g.node, `"${l}" is not a variant of ${showType(baseT)}`);
        if (g.labels.length === 1) {
          const v = u.variants.find((v) => v.lit === g.labels[0])!;
          covered.add(v.lit);
          let e1 = env;
          const names: string[] = [];
          const fields = new Map<string, Val>();
          for (const f of v.fields) {
            const r = freshLocal(e1, leanIdent(f.name));
            e1 = r.env;
            names.push(r.name);
            fields.set(f.name, { code: r.name, type: f.type });
          }
          const narrow = new Map(e1.narrow);
          if (key) narrow.set(key, { kind: "variant", code: target.code, type: baseT, variant: v.lit, fields });
          arms += `\n  | .${leanField(v.ctor)}${names.map((n) => " " + n).join("")} => ${paren(block(g.body, 0, { ...e1, narrow }, bc, after))}`;
        } else {
          const pats = g.labels.map((l) => {
            const v = u.variants.find((v) => v.lit === l)!;
            covered.add(l);
            return `.${leanField(v.ctor)}${v.fields.map(() => " _").join("")}`;
          });
          arms += `\n  | ${pats.join(" | ")} => ${paren(block(g.body, 0, env, bc, after))}`;
        }
        if (g.isDefault) hasDefault = true;
      }
      if (!hasDefault && covered.size < u.variants.length) arms += `\n  | _ => ${paren(rest(env))}`;
      return `(match ${h} : ${target.code} with${arms})`;
    }
  }
  // switch on an enum value: exhaustive match on its constructors
  const dv = expr(disc, env);
  if (dv.type.k === "enum") {
    const lits = m.reg.enumLits(dv.type);
    const covered = new Set<string>();
    let arms = "";
    let hasDefault = false;
    for (const g of groups) {
      if (g.isDefault && g.labels.length === 0) {
        hasDefault = true;
        arms += `\n  | _ => ${paren(block(g.body, 0, env, bc, after))}`;
        continue;
      }
      for (const l of g.labels) if (!lits.includes(l)) fail(g.node, `"${l}" is not a member of ${showType(dv.type)}`);
      g.labels.forEach((l) => covered.add(l));
      arms += `\n  | ${g.labels.map((l) => `.${leanField(l)}`).join(" | ")} => ${paren(block(g.body, 0, env, bc, after))}`;
      if (g.isDefault) hasDefault = true;
    }
    if (!hasDefault && covered.size < lits.length) arms += `\n  | _ => ${paren(rest(env))}`;
    const h = m.fresh("h");
    return `(match ${h} : ${dv.code} with${arms})`;
  }
  // generic switch on a primitive value: if-chain
  let code: string | null = null;
  const defaultGroup = groups.find((g) => g.isDefault);
  let elseCode = defaultGroup ? block(defaultGroup.body, 0, env, bc, after) : rest(env);
  for (const g of [...groups].reverse()) {
    if (g.labels.length === 0) continue;
    const conds = g.labels.map((l) => {
      const lv = dv.type.k === "enum" ? `${dv.type.name}.${leanField(l)}` : dv.type.k === "str" ? jsStr(l) : l;
      return `VReact.JS.eq ${paren(dv.code)} ${paren(lv)}`;
    });
    const h = m.fresh("h");
    elseCode = `(if ${h} : (${conds.join(" || ")}) = true then ${paren(block(g.body, 0, env, bc, after))} else ${paren(elseCode)})`;
  }
  code = elseCode;
  return code;
}

function terminates(stmts: readonly ts.Statement[]): boolean {
  const last = stmts[stmts.length - 1];
  if (!last) return false;
  if (ts.isReturnStatement(last) || ts.isThrowStatement(last)) return true;
  if (ts.isBlock(last)) return terminates(last.statements);
  if (ts.isIfStatement(last)) return !!last.elseStatement && terminates(blockOf(last.thenStatement)) && terminates(blockOf(last.elseStatement));
  return false;
}

/** for (const x of xs) { … } — a fold whose accumulator is the tuple of locals assigned in the body. */
function forOf(s: ts.ForOfStatement, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  const m = env.m;
  if (!ts.isVariableDeclarationList(s.initializer) || s.initializer.declarations.length !== 1) fail(s, "use for (const x of xs)");
  const xs = expr(s.expression, env);
  if (xs.type.k !== "arr") fail(s.expression, "for…of over a non-array");
  // locals assigned in the body
  const assigned: ts.Symbol[] = [];
  const visit = (n: ts.Node) => {
    if (ts.isBinaryExpression(n) && [ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.MinusEqualsToken].includes(n.operatorToken.kind) && ts.isIdentifier(n.left)) {
      const sym = symbolOf(env, n.left);
      if (sym && env.vars.has(sym) && !assigned.includes(sym)) assigned.push(sym);
    }
    if ((ts.isPostfixUnaryExpression(n) || ts.isPrefixUnaryExpression(n)) && ts.isIdentifier(n.operand) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) {
      const sym = symbolOf(env, n.operand);
      if (sym && env.vars.has(sym) && !assigned.includes(sym)) assigned.push(sym);
    }
    if (ts.isReturnStatement(n) || ts.isBreakStatement(n) || ts.isContinueStatement(n)) fail(n, "return/break/continue inside for…of are not supported; use array methods (find, some, …)");
    if (ts.isCallExpression(n) && updateTarget(n.expression, env)) fail(n, "state updates inside loops are not supported; compute the new value, then update once");
    ts.forEachChild(n, visit);
  };
  visit(s.statement);
  if (assigned.length === 0) fail(s, "loop has no effect (it assigns no local variable)");
  const accTypes = assigned.map((sym) => (env.vars.get(sym) as { type: VType }).type);
  const accCodes = assigned.map((sym) => (env.vars.get(sym) as { code: string }).code);
  // fresh names for accumulator and element
  let e1 = env;
  const accNames: string[] = [];
  for (const sym of assigned) {
    const r = freshLocal(e1, leanIdent(sym.name));
    e1 = r.env;
    accNames.push(r.name);
    e1 = bind(e1, sym, { k: "val", code: r.name, type: (env.vars.get(sym) as { type: VType }).type });
  }
  const decl = s.initializer.declarations[0];
  const pr = bindParam(decl.name, xs.type.elem, e1);
  const tuple = (names: string[]) => (names.length === 1 ? names[0] : `(${names.join(", ")})`);
  const bodyBc: BlockCtx = { kind: "value", fnNode: s, onReturn: () => fail(s, "return inside loop") };
  const body = block(blockOf(s.statement), 0, pr.env, bodyBc, (e3) => tuple(assigned.map((sym) => (e3.vars.get(sym) as { code: string }).code)));
  const accT = accTypes.length === 1 ? leanType(accTypes[0]) : `(${accTypes.map(leanType).join(" × ")})`;
  const fold = `(${paren(xs.code)}.foldl (fun (acc : ${accT}) ${pr.binder} => let ${tuple(accNames)} := acc; ${body}) ${tuple(accCodes)})`;
  // rebind the assigned locals after the loop
  let e4 = env;
  const outNames: string[] = [];
  for (const sym of assigned) {
    const r = freshLocal(e4, leanIdent(sym.name));
    e4 = bind(r.env, sym, { k: "val", code: r.name, type: (env.vars.get(sym) as { type: VType }).type });
    outNames.push(r.name);
  }
  return `(let ${tuple(outNames)} := ${fold};\n${rest(e4)})`;
}

/* ─────────────────────────── handlers ─────────────────────────── */

/** Translate a function used as an event handler into `fun ev => outcome`. */
export function handlerFn(fnExpr: ts.Expression, env: Env, kind: "discrete" | "robust", argTypes: Param[] | "event", hyps?: string): { code: string; params: string[] } {
  const m = env.m;
  const comp = env.comp!;
  fnExpr = stripParens(fnExpr);
  // passing a closure by name
  if (ts.isIdentifier(fnExpr)) {
    const s = symbolOf(env, fnExpr);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "closure") return handlerFn(b.fn, { ...b.env, scope: env.scope }, kind, argTypes, hyps);
    if (b?.k === "callback") {
      // forward a parent callback
      const cb = comp.info.callbacks.find((c) => c.name === b.cb.name)!;
      return forwardCallback(cb, fnExpr, env, kind, argTypes);
    }
    fail(fnExpr, "expected a function (inline arrow, local handler, or callback prop)");
  }
  if (ts.isPropertyAccessExpression(fnExpr) && ts.isIdentifier(fnExpr.expression)) {
    const s = symbolOf(env, fnExpr.expression);
    if (s && env.vars.get(s)?.k === "props") {
      const cb = comp.info.callbacks.find((c) => c.name === fnExpr.name.text);
      if (!cb) fail(fnExpr, `props.${fnExpr.name.text} is not a callback`);
      return forwardCallback(cb, fnExpr, env, kind, argTypes);
    }
  }
  if (!ts.isArrowFunction(fnExpr) && !ts.isFunctionExpression(fnExpr)) fail(fnExpr, "expected a function");
  const acc: HandlerAcc = { kind, updates: [], emit: null, eventVar: null };
  let e1: Env = { ...env, handler: acc, curState: undefined };
  const params: string[] = [];
  if (argTypes === "event") {
    if (fnExpr.parameters.length > 1) fail(fnExpr, "DOM event handlers take at most one parameter (the event)");
    const p = fnExpr.parameters[0];
    if (p) {
      if (!ts.isIdentifier(p.name)) fail(p, "destructuring the event object is not supported");
      const r = freshLocal(e1, leanIdent(p.name.text));
      e1 = bind(r.env, symbolOf(env, p.name)!, { k: "event", leanVar: r.name });
      params.push(r.name);
    } else {
      const r = freshLocal(e1, "ev");
      e1 = r.env;
      params.push("_");
    }
  } else {
    if (fnExpr.parameters.length !== argTypes.length) fail(fnExpr, `callback expects ${argTypes.length} parameters`);
    fnExpr.parameters.forEach((p, i) => {
      const r = bindParam(p.name, argTypes[i].type, e1);
      e1 = r.env;
      params.push(r.binder);
    });
  }
  const done = (e3: Env) => outcome(e3.handler!, comp);
  const bc: BlockCtx = { kind: "handler", fnNode: fnExpr, onDone: done };
  let body: string;
  if (ts.isBlock(fnExpr.body)) body = block(fnExpr.body.statements, 0, e1, bc, done);
  else body = exprStatement(fnExpr.body, e1, bc, done);
  return { code: body, params };
}

export function outcome(h: HandlerAcc, comp: CompCtx): string {
  const upd = `[${h.updates.join(",\n    ")}]`;
  const emit = h.emit ? `(some ${h.emit})` : "none";
  return `(VReact.Outcome.mk (S := ${comp.stateType}) (E := E) ${upd} ${emit})`;
}

function forwardCallback(cb: { name: string; params: Param[] }, node: ts.Node, env: Env, kind: "discrete" | "robust", argTypes: Param[] | "event"): { code: string; params: string[] } {
  const comp = env.comp!;
  if (kind === "robust") fail(node, "parent callbacks cannot be invoked from continuous events / effects");
  const ps = argTypes === "event" ? [] : argTypes;
  if (argTypes === "event" && cb.params.length) fail(node, `${cb.name} needs arguments; wrap it: () => ${cb.name}(…)`);
  if (argTypes !== "event" && ps.length !== cb.params.length) fail(node, `callback arity mismatch forwarding ${cb.name}`);
  let e1 = env;
  const names: string[] = [];
  for (const p of ps) {
    const r = freshLocal(e1, leanIdent(p.name));
    e1 = r.env;
    names.push(r.name);
  }
  const ob = env.m.ob(node, "callback-contract", `contract of forwarded callback ${cb.name}`);
  const emit = `(${comp.cbVar}.${leanField(cb.name)}${names.map((n) => " " + n).join("")} ${ob})`;
  return { code: `(VReact.Outcome.mk (S := ${comp.stateType}) (E := E) [] (some ${emit}))`, params: argTypes === "event" ? ["_"] : names };
}

/** React hook dependency check (exhaustive deps). */
export function checkDeps(fn: ts.ArrowFunction | ts.FunctionExpression, depsArg: ts.Expression | undefined, env: Env, hook: string) {
  if (!depsArg) {
    if (hook === "useEffect") return;
    fail(fn, `${hook} needs a dependency array`);
  }
  if (!ts.isArrayLiteralExpression(depsArg)) fail(depsArg, "dependency list must be an array literal");
  const listed = new Set<string>();
  for (const d of depsArg.elements) {
    const k = pathKey(env, d);
    if (!k) fail(d, "dependencies must be identifiers or property paths");
    listed.add(k);
  }
  const missing: string[] = [];
  const visit = (n: ts.Node) => {
    if (ts.isIdentifier(n) && !(ts.isPropertyAccessExpression(n.parent) && n.parent.name === n)) {
      const s = symbolOf(env, n);
      const b = s ? env.vars.get(s) : undefined;
      if (b && (b.k === "val" || b.k === "closure" || b.k === "callback")) {
        // reactive value: covered if it, or a path starting with it, is listed
        let full: ts.Expression = n;
        while (ts.isPropertyAccessExpression(full.parent) && full.parent.expression === full) full = full.parent;
        const k1 = pathKey(env, n)!;
        const kFull = pathKey(env, full);
        const covered = listed.has(k1) || (kFull && [...listed].some((l) => kFull === l || kFull.startsWith(l + ".")));
        if (!covered && !missing.includes(n.text)) missing.push(n.text);
      }
      if (b?.k === "props") {
        let full: ts.Expression = n;
        while (ts.isPropertyAccessExpression(full.parent) && full.parent.expression === full) full = full.parent;
        const kFull = pathKey(env, full);
        const covered = kFull && [...listed].some((l) => kFull === l || kFull.startsWith(l + ".") || l === pathKey(env, n));
        if (!covered && !missing.includes(full.getText())) missing.push(full.getText());
      }
    }
    ts.forEachChild(n, visit);
  };
  visit(fn.body);
  if (missing.length) fail(depsArg, `${hook} is missing dependencies: ${missing.join(", ")} (stale closures)`);
}
