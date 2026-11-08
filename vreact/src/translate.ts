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
import { T, type VType, type Field, type Param, sameType, showType, leanType, sharedFields, type Variant, typeOfNode, kindsOfType, nullShape } from "./types.ts";
import { type Env, type Val, ModCtx, type Binding, type StateVar, type CompCtx, type HandlerAcc, type FnInfo, type CompInfo, type Global, type Narrowed, bind, extend, freshLocal } from "./ctx.ts";
import { VtsError, fail, leanField, leanAccessor, leanIdent, leanStr, jsStr, leanInt, paren, nodeText, capitalize } from "./util.ts";

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

/* ─────────────────── closures and mutable locals ─────────────────── */

/** Array methods whose callback runs immediately (during the call). */
const IMMEDIATE_METHODS = new Set(["map", "filter", "some", "every", "find", "findIndex", "reduce", "flatMap", "toSorted"]);
/** vreact/spec functions whose function argument is a predicate evaluated in place. */
const SPEC_LAMBDAS = new Set(["forall", "exists", "distinct", "ensures", "callbackRequires"]);

/** The `let` declaration of a local variable symbol, if it is one. */
function letDecl(s: ts.Symbol | undefined): ts.VariableDeclaration | null {
  const d = s?.valueDeclaration;
  if (d && ts.isVariableDeclaration(d) && ts.isVariableDeclarationList(d.parent) && d.parent.flags & ts.NodeFlags.Let) return d;
  return null;
}

/** The variable an identifier refers to (shorthand properties `{ x }` resolve to the variable `x`). */
function varSymbol(checker: ts.TypeChecker, id: ts.Identifier): ts.Symbol | undefined {
  if (ts.isShorthandPropertyAssignment(id.parent) && id.parent.name === id) return checker.getShorthandAssignmentValueSymbol(id.parent);
  return checker.getSymbolAtLocation(id);
}

/** Is `id` the target of an assignment, compound assignment, `++` or `--`? */
function isWriteTarget(id: ts.Identifier): boolean {
  let n: ts.Node = id;
  while (ts.isParenthesizedExpression(n.parent)) n = n.parent;
  const p = n.parent;
  if (ts.isBinaryExpression(p) && p.left === n) {
    const k = p.operatorToken.kind;
    return k >= ts.SyntaxKind.FirstAssignment && k <= ts.SyntaxKind.LastAssignment;
  }
  if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p)) && (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken)) return true;
  return false;
}

function within(n: ts.Node, outer: ts.Node): boolean {
  return n.pos >= outer.pos && n.end <= outer.end;
}

/**
 * Is `fn` called immediately where it is written (array-method callbacks, spec
 * predicates, `useMemo` / `useState` initialisers)?  Every other function value —
 * local helpers, handlers, callback props, functional updates `setX(prev => …)`,
 * effects, timer callbacks, cleanups, `useCallback` — runs later.
 */
function isImmediateFn(fn: ts.ArrowFunction | ts.FunctionExpression, env: Env): boolean {
  let child: ts.Node = fn;
  while (ts.isParenthesizedExpression(child.parent)) child = child.parent;
  const p = child.parent;
  if (!ts.isCallExpression(p) || !p.arguments.includes(child as ts.Expression)) return false;
  const callee = p.expression;
  if (ts.isPropertyAccessExpression(callee) && IMMEDIATE_METHODS.has(callee.name.text)) return true;
  const sf = specFn(env, callee);
  if (sf && SPEC_LAMBDAS.has(sf)) return true;
  const h = hookName(env, callee);
  return (h === "useMemo" || h === "useState") && p.arguments[0] === child;
}

/**
 * JS closures capture variables, not values, while the translation gives a
 * function body the environment of the point where the function is created.
 * The two agree exactly when (a) no function that runs later reads a `let`
 * that may be reassigned after the function was created, and (b) no function
 * assigns a `let` declared outside it.  Both are checked here for one
 * top-level function or component body (a `let` is only visible inside it).
 */
export function checkClosures(body: ts.Node, env: Env) {
  const checker = env.m.checker;
  const writes = new Map<ts.Symbol, ts.Node[]>();
  const collectWrites = (n: ts.Node) => {
    if (ts.isIdentifier(n) && isWriteTarget(n)) {
      const s = checker.getSymbolAtLocation(n);
      if (s && letDecl(s)) writes.set(s, [...(writes.get(s) ?? []), n]);
    }
    ts.forEachChild(n, collectWrites);
  };
  collectWrites(body);
  /** May a write to `s` execute after `fn` has been created? */
  const laterWrite = (s: ts.Symbol, decl: ts.Node, fn: ts.Node): boolean => {
    const ws = writes.get(s) ?? [];
    if (ws.some((w) => w.getStart() >= fn.end)) return true;
    // a loop around the function (but inside the variable's scope) runs earlier writes again
    for (let a: ts.Node | undefined = fn.parent; a && a !== body; a = a.parent) {
      if (ts.isForOfStatement(a) && !within(decl, a) && ws.some((w) => within(w, a))) return true;
    }
    return false;
  };
  const stack: { fn: ts.ArrowFunction | ts.FunctionExpression; immediate: boolean }[] = [];
  const visit = (n: ts.Node) => {
    if (ts.isArrowFunction(n) || ts.isFunctionExpression(n)) {
      stack.push({ fn: n, immediate: isImmediateFn(n, env) });
      ts.forEachChild(n, visit);
      stack.pop();
      return;
    }
    if (ts.isIdentifier(n) && stack.length) {
      const s = varSymbol(checker, n);
      const d = letDecl(s);
      if (s && d) {
        for (let i = stack.length - 1; i >= 0; i--) {
          const { fn, immediate } = stack[i];
          if (within(d, fn)) break; // declared inside this function (and so inside the outer ones)
          if (isWriteTarget(n)) {
            fail(n, `\`${n.text}\` is a \`let\` declared outside this function: assigning it from inside a function or callback is not supported (the write would be lost in the translation). Compute the new value outside the callback, e.g. with for…of or reduce`);
          }
          if (!immediate && laterWrite(s, d, fn)) {
            fail(n, `this function reads \`${n.text}\`, which is reassigned after the function is created; a JS closure sees the variable's latest value when it runs, not its value here. Copy it first (\`const ${n.text}Now = ${n.text};\`) and use the copy, or move the assignment before the function`);
          }
        }
      }
    }
    ts.forEachChild(n, visit);
  };
  visit(body);
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

/**
 * The narrowing in effect in `env` on the paths rooted at the given variables, keyed by
 * path text (`s`, `s.inner`): what `vreact synth` may assume at a hole.
 */
export function narrowingAt(env: Env, roots: readonly { sym: ts.Symbol; name: string }[]): Map<string, Narrowed> {
  const out = new Map<string, Narrowed>();
  for (const { sym, name } of roots) {
    const k = `#${symId(sym)}`;
    for (const [key, n] of env.narrow) if (key === k || key.startsWith(k + ".")) out.set(name + key.slice(k.length), n);
  }
  return out;
}

/** `remaining` (see Env) on the paths rooted at the given variables, keyed by path text as narrowingAt. */
export function remainingAt(env: Env, roots: readonly { sym: ts.Symbol; name: string }[]): Map<string, string[]> {
  const out = new Map<string, string[]>();
  for (const { sym, name } of roots) {
    const k = `#${symId(sym)}`;
    for (const [key, vs] of env.remaining ?? []) if (key === k || key.startsWith(k + ".")) out.set(name + key.slice(k.length), vs);
  }
  return out;
}

/** Is `e` (a variable or property path) narrowed to a non-null value here (to a variant: also present)? */
function narrowedSome(env: Env, e: ts.Expression): boolean {
  const k = pathKey(env, e);
  const n = k ? env.narrow.get(k) : undefined;
  return !!n && (n.kind === "some" || n.kind === "variant");
}

function isNullLit(e: ts.Expression): boolean {
  return e.kind === ts.SyntaxKind.NullKeyword || (ts.isIdentifier(e) && e.text === "undefined");
}

function stripParens(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) && e.type.getText() === "const") e = ts.isParenthesizedExpression(e) ? e.expression : (e as ts.AsExpression).expression;
  return e;
}

/** A conditional expression with a `null`/`undefined` leaf (`c ? x : null`, `c ? x : d ? y : null`). */
function hasNullLeaf(e: ts.Expression): boolean {
  e = stripParens(e);
  if (isNullLit(e)) return true;
  return ts.isConditionalExpression(e) && (hasNullLeaf(e.whenTrue) || hasNullLeaf(e.whenFalse));
}

/** The type of some non-null leaf of a conditional (typed in its narrowed environment, nothing emitted). */
function nonNullLeafType(e: ts.Expression, env: Env): VType | undefined {
  e = stripParens(e);
  if (isNullLit(e)) return undefined;
  if (ts.isConditionalExpression(e) && hasNullLeaf(e)) {
    let ot: VType | undefined;
    const c = e;
    const dry = { ...env, m: dryCtx(env.m) };
    branch(c.condition, dry, (e1) => {
      ot = ot ?? nonNullLeafType(c.whenTrue, e1);
      return "_";
    }, (e2) => {
      ot = ot ?? nonNullLeafType(c.whenFalse, e2);
      return "_";
    });
    return ot;
  }
  return typeOf(e, env);
}

/**
 * The TypeScript type of an expression (the source of truth for which nullish value,
 * `null` or `undefined`, an optional value can be: VTS represents both as `none`).
 * `ensures((r) => …)` types its parameter `any`; the function's declared return type is used
 * instead (and for `r.f`, `r[i]`, and a callback parameter of `r.every(…)`, the types they have
 * in it).  `null` when unknown.
 */
function tsTypeOf(e: ts.Expression, env: Env): ts.Type | null {
  const ck = env.m.checker;
  e = stripParens(e);
  const t = ck.getTypeAtLocation(e);
  if (!(t.flags & ts.TypeFlags.Any)) return t;
  if (ts.isIdentifier(e)) {
    // (the name of a shorthand field `{ r }` stands for the variable `r`)
    const s = ts.isShorthandPropertyAssignment(e.parent) && e.parent.name === e ? symbolOf(env, e.parent) : symbolOf(env, e);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "val" && b.ts && !(b.ts.flags & ts.TypeFlags.Any)) return b.ts;
    const rt = ensuresResultType(s, env);
    return rt ? ck.getTypeFromTypeNode(rt) : null;
  }
  if (ts.isPropertyAccessExpression(e) && !e.questionDotToken) {
    const base = tsTypeOf(e.expression, env);
    if (!base) return null;
    const p = ck.getPropertyOfType(ck.getNonNullableType(base), e.name.text);
    return p ? ck.getTypeOfSymbolAtLocation(p, e) : null;
  }
  if (ts.isElementAccessExpression(e) && !e.questionDotToken) {
    const base = tsTypeOf(e.expression, env);
    if (!base) return null;
    if (ck.isTupleType(base)) {
      const i = stripParens(e.argumentExpression);
      const args = ck.getTypeArguments(base as ts.TypeReference);
      return ts.isNumericLiteral(i) && /^\d+$/.test(i.text) && Number(i.text) < args.length ? args[Number(i.text)] : null;
    }
    return ck.getIndexTypeOfType(base, ts.IndexKind.Number) ?? null;
  }
  return null;
}

/** For the parameter of an unannotated `ensures((r) => …)`: the declared return type of its function. */
function ensuresResultType(s: ts.Symbol | undefined, env: Env): ts.TypeNode | null {
  const d = s?.valueDeclaration;
  if (d && ts.isParameter(d) && !d.type && (ts.isArrowFunction(d.parent) || ts.isFunctionExpression(d.parent))) {
    const call = d.parent.parent;
    if (ts.isCallExpression(call) && specFn(env, call.expression) === "ensures") {
      let f: ts.Node | undefined = call;
      while (f && !ts.isFunctionDeclaration(f)) f = f.parent;
      return (f && (f as ts.FunctionDeclaration).type) ?? null;
    }
  }
  return null;
}

/** Whether a TypeScript type is, or has a part (element, field, parameter, result) that is, `any`. */
function containsAny(t: ts.Type, ck: ts.TypeChecker, seen = new Set<ts.Type>()): boolean {
  if (t.flags & ts.TypeFlags.Any) return true;
  if (seen.has(t)) return false;
  seen.add(t);
  if (t.isUnionOrIntersection()) return t.types.some((p) => containsAny(p, ck, seen));
  if (!(t.flags & ts.TypeFlags.Object)) return false;
  if (ck.isArrayType(t) || ck.isTupleType(t)) return ck.getTypeArguments(t as ts.TypeReference).some((a) => containsAny(a, ck, seen));
  for (const sig of ck.getSignaturesOfType(t, ts.SignatureKind.Call)) {
    if (containsAny(sig.getReturnType(), ck, seen)) return true;
    if (sig.getParameters().some((p) => p.valueDeclaration && containsAny(ck.getTypeOfSymbolAtLocation(p, p.valueDeclaration), ck, seen))) return true;
  }
  // object literal types (`{ v: r }`); named records, unions and enums have declared field types
  if ((t as ts.ObjectType).objectFlags & ts.ObjectFlags.ObjectLiteral) {
    return ck.getPropertiesOfType(t).some((p) => p.valueDeclaration !== undefined && containsAny(ck.getTypeOfSymbolAtLocation(p, p.valueDeclaration), ck, seen));
  }
  return false;
}

/**
 * A value whose TypeScript type is (or contains) `any` (the parameter of an unannotated
 * `ensures((r) => …)`, and what is computed from it: `r.v`, `r[0]`, `r.find(…)`, the
 * parameter of a callback of `r.every(…)`, `[r]`) where TypeScript checks a type (an argument,
 * an element, a field, an initializer): TypeScript accepts it whatever it is, but the code it goes
 * to reads that type to tell `null` from `undefined` (both `none` in VTS).  So each optional
 * part of the value must have the nullish value the type there says (`isNull(x: int | null)`
 * applied to an `int | undefined` result would be proved true for `undefined`).
 */
function checkUncheckedValue(e: ts.Expression, v: Val, env: Env) {
  if (!hasOptPart(v.type)) return;
  const ck = env.m.checker;
  if (!containsAny(ck.getTypeAtLocation(e), ck)) return;
  // operands whose nullish value is consumed, not passed on: `r ?? d`, `r || d`, `r!`, `case r:`
  let n: ts.Node = e;
  while (ts.isParenthesizedExpression(n.parent)) n = n.parent;
  const p = n.parent;
  if (ts.isNonNullExpression(p) || ts.isCaseClause(p)) return;
  if (ts.isBinaryExpression(p) && p.left === n && (p.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken || p.operatorToken.kind === ts.SyntaxKind.BarBarToken)) return;
  const slot = ck.getContextualType(e);
  if (!slot || slot.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return;
  const real = tsTypeOf(e, env);
  const a = real && nullShape(real, v.type, ck);
  const b = nullShape(slot, v.type, ck);
  if (a !== null && b !== null && a === b) return;
  const what = nodeText(e, 40);
  const has = real && a !== null ? `a value of type \`${showWithKinds(v.type, real, env)}\`` : `a value of type \`${showType(v.type)}\` (whether null or undefined: unknown)`;
  // the variable it is computed from (`r` in `r.v[0]`, `r.find(…)`)
  let root: ts.Expression = stripParens(e);
  while (ts.isPropertyAccessExpression(root) || ts.isElementAccessExpression(root) || ts.isCallExpression(root) || ts.isNonNullExpression(root)) root = stripParens(root.expression);
  const rs = ts.isIdentifier(root) ? (ts.isShorthandPropertyAssignment(root.parent) && root.parent.name === root ? symbolOf(env, root.parent) : symbolOf(env, root)) : undefined;
  const rt = ensuresResultType(rs, env);
  const fix = rt && ts.isIdentifier(root)
    ? `annotate the result parameter with the return type, ensures((${root.text}: ${nodeText(rt, 50)}) => …), so that TypeScript checks it`
    : `give the parameter it comes from its exact type, so that TypeScript checks it`;
  fail(e, `\`${what}\` has TypeScript type any, so TypeScript does not check it against the type \`${ck.typeToString(slot)}\` expected here (that type says whether a missing value is null or undefined), and it is ${has}: ${fix}`);
}

function nullishKinds(e: ts.Expression, env: Env): { null: boolean; undef: boolean } | null {
  const t = tsTypeOf(e, env);
  return t ? kindsOfType(t) : null;
}

/**
 * `x === null` / `x === undefined` (strict) must test the nullish value `x` can actually
 * hold: JS `undefined === null` is false.  `== null` / `!= null` cover both.
 */
function checkStrictNullTest(node: ts.Node, other: ts.Expression, lit: ts.Expression, op: ts.SyntaxKind, env: Env) {
  if (op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken) return;
  const what = nodeText(other, 40);
  const litText = lit.kind === ts.SyntaxKind.NullKeyword ? "null" : "undefined";
  const k = nullishKinds(other, env);
  if (!k) fail(node, `cannot tell whether \`${what}\` may be null or undefined (its TypeScript type is any or unknown): give it its exact type (e.g. ensures((r: T | null) => …)) or compare with == null`);
  if (k.null && k.undef) fail(node, `\`${what}\` may be null or undefined, which VTS does not distinguish: compare with == null / != null`);
  if (litText === "null" && k.undef && !k.null) {
    fail(node, `\`${what}\` can be undefined but never null (optional fields, find(), at() and ?. give undefined), so \`=== null\` is always false in JS: write === undefined or == null`);
  }
  if (litText === "undefined" && k.null && !k.undef) {
    fail(node, `\`${what}\` can be null but never undefined, so \`=== undefined\` is always false in JS: write === null or == null`);
  }
}

/** `a === b` on two possibly-nullish values: both must use the same nullish value (null !== undefined). */
function checkOptionalEquality(node: ts.Node, a: ts.Expression, b: ts.Expression, env: Env) {
  const ka = nullishKinds(a, env);
  const kb = nullishKinds(b, env);
  if (!ka || !kb) fail(node, `cannot tell whether the operands may be null or undefined (TypeScript type any or unknown): give them their exact types`);
  const any = (k: { null: boolean; undef: boolean }) => k.null || k.undef;
  if (!any(ka) || !any(kb)) return;
  if ((ka.null && ka.undef) || (kb.null && kb.undef) || ka.null !== kb.null) {
    fail(node, `\`${nodeText(node, 50)}\` compares values that may be null and undefined (null !== undefined in JS, but VTS represents both as absent): narrow with != null first`);
  }
}

/** Values JS compares by value (`===`, SameValueZero in includes/indexOf/Set): booleans, ints, strings, enums. */
function isPrimitiveEq(t: VType): boolean {
  if (t.k === "opt") return isPrimitiveEq(t.elem);
  return t.k === "bool" || t.k === "int" || t.k === "str" || t.k === "enum";
}

/** Element comparisons of `includes`/`indexOf`/`distinct` are by value only for primitive elements. */
function checkPrimitiveElems(node: ts.Node, arr: ts.Expression, elem: VType, what: string, env: Env) {
  if (elem.k === "num") fail(node, `${what} on number elements is not supported (JS compares the elements with SameValueZero or ===, where NaN and -0 are special; numbers are opaque in VTS); use ints`);
  if (!isPrimitiveEq(elem)) {
    fail(node, `${what} on ${showType(elem)} elements compares object identity in JS (a copy is never found): compare keys instead, e.g. xs.some((x) => x.id === v.id)`);
  }
  if (elem.k === "opt") {
    const et = elemTsType(arr, env);
    const k = et ? kindsOfType(et) : null;
    if (!k || (k.null && k.undef)) fail(node, `${what} on elements that may be null or undefined is not supported (VTS does not distinguish them)`);
  }
}

/** The TypeScript type of the elements of an array expression (null when unknown). */
function elemTsType(arr: ts.Expression, env: Env): ts.Type | null {
  const t = tsTypeOf(arr, env);
  return (t && env.m.checker.getIndexTypeOfType(t, ts.IndexKind.Number)) ?? null;
}

/**
 * The parameter types of a function type (its single call signature; in a union such as
 * `SetStateAction<T> = T | ((prev: T) => T)`, of its only function member).  null when there is
 * no such signature, or it has a rest parameter.
 */
export function fnParamTsTypes(t: ts.Type | undefined, at: ts.Node, env: Env): ts.Type[] | null {
  if (!t) return null;
  const ck = env.m.checker;
  const sigs = (t.isUnion() ? t.types : [t]).flatMap((m) => ck.getSignaturesOfType(m, ts.SignatureKind.Call));
  if (sigs.length !== 1) return null;
  const ps = sigs[0].getParameters();
  if (ps.some((p) => { const d = p.valueDeclaration; return !!d && ts.isParameter(d) && !!d.dotDotDotToken; })) return null;
  return ps.map((p) => ck.getTypeOfSymbolAtLocation(p, at));
}

/** The types the context of a function expression (call argument, JSX attribute, …) gives its parameters. */
export function contextualParamTsTypes(fn: ts.Expression, env: Env): ts.Type[] | null {
  return fnParamTsTypes(env.m.checker.getContextualType(fn), fn, env);
}

/** Whether a VTS type has an optional part (whose nullish value, null or undefined, only TypeScript types tell). */
function hasOptPart(t: VType): boolean {
  if (t.k === "opt") return true;
  if (t.k === "arr") return hasOptPart(t.elem);
  if (t.k === "tuple") return t.elems.some(hasOptPart);
  return false; // records, unions, enums: nominal (their fields' kinds are those of the declaration)
}

/** `showType`, with the nullish value (null or undefined) of each optional part as TypeScript types it. */
function showWithKinds(vt: VType, t: ts.Type | null, env: Env): string {
  const ck = env.m.checker;
  const k = vt.k === "opt" && t ? kindsOfType(t) : null;
  if (vt.k === "opt" && t && k) {
    const inner = showWithKinds(vt.elem, ck.getNonNullableType(t), env);
    return [inner, ...(k.null ? ["null"] : []), ...(k.undef ? ["undefined"] : [])].join(" | ");
  }
  if (vt.k === "arr" && t) {
    const et = ck.getIndexTypeOfType(t, ts.IndexKind.Number) ?? null;
    const inner = showWithKinds(vt.elem, et, env);
    return `readonly ${vt.elem.k === "opt" || vt.elem.k === "fn" ? `(${inner})` : inner}[]`;
  }
  if (vt.k === "tuple" && t && ck.isTupleType(t)) {
    const args = ck.getTypeArguments(t as ts.TypeReference);
    return `[${vt.elems.map((e, i) => showWithKinds(e, args[i] ?? null, env)).join(", ")}]`;
  }
  return showType(vt);
}

/**
 * A parameter of a function value whose argument TypeScript does not check against the
 * parameter's annotation: `ensures` takes `(result: any) => boolean`, and for a callback (array
 * method, handler, functional update, contract lambda) TypeScript only requires the annotation
 * to be a supertype of what is passed (`unknown`, `int | null` for an `int` argument).  The
 * translation types the parameter from the value it receives (`real`, of TypeScript type
 * `realTs`), but the null/undefined checks read TypeScript types: so the annotation must be
 * exactly that type (the same VTS type and, at every optional position, the same nullish value).
 * Default values and rest parameters are rejected (a default replaces an `undefined` argument).
 */
export function checkParamAnnotation(p: ts.ParameterDeclaration, real: VType, realTs: ts.Type | null, env: Env) {
  const pname = p.name.getText();
  if (p.dotDotDotToken) fail(p, `rest parameters are not supported`);
  if (p.initializer) fail(p.initializer, `a default value for parameter \`${pname}\` is not supported (JS uses it when the argument is undefined)`);
  if (p.questionToken) fail(p, `optional parameter \`${pname}?\` is not supported`);
  if (!p.type) return;
  const ck = env.m.checker;
  const want = showWithKinds(real, realTs, env);
  const reject = (): never =>
    fail(p.type!, `parameter \`${pname}\` is annotated \`${nodeText(p.type!, 50)}\` but receives a value of type \`${want}\`: give it exactly that type, or leave the annotation out (the translation types \`${pname}\` from the value it receives, and TypeScript does not check that the two agree)`);
  let ann: VType;
  try {
    ann = typeOfNode(p.type, env.m.prog.typeEnv, "Param" + capitalize(pname.replace(/[^A-Za-z0-9_]/g, "")));
  } catch (e) {
    if (e instanceof VtsError) reject();
    throw e;
  }
  if (!annotationFits(ann!, real)) reject();
  if (!hasOptPart(real)) return;
  if (!realTs) fail(p.type, `cannot check the annotation \`${nodeText(p.type, 50)}\` of parameter \`${pname}\` against the value it receives (whether it is null or undefined): leave the annotation out`);
  const a = nullShape(ck.getTypeFromTypeNode(p.type), real, ck);
  const b = nullShape(realTs, real, ck);
  if (a === null || b === null || a !== b) reject();
}

/**
 * Whether an annotation of VTS type `ann` is exact for a value of VTS type `real`: the same type,
 * except that `number` may annotate an int (a map index, a forall variable): `int` is
 * TypeScript's `number`, so TypeScript reads the two alike, and the translation uses `real`.
 */
function annotationFits(ann: VType, real: VType): boolean {
  if (ann.k === "num" && real.k === "int") return true;
  if ((ann.k === "opt" && real.k === "opt") || (ann.k === "arr" && real.k === "arr")) return annotationFits(ann.elem, real.elem);
  if (ann.k === "tuple" && real.k === "tuple") return ann.elems.length === real.elems.length && ann.elems.every((e, i) => annotationFits(e, real.elems[i]));
  return sameType(ann, real);
}

/** `distinct(xs, key)` compares keys with SameValueZero (a JS Set): keys must be ints or strings. */
function checkDistinctKey(node: ts.Node, t: VType) {
  if (t.k !== "int" && t.k !== "str" && t.k !== "enum") fail(node, `distinct keys must be int or string (got ${showType(t)})`);
}

/** Exact arity of a modelled library call (extra arguments would be silently ignored otherwise). */
function arity(c: ts.CallExpression, what: string, min: number, max: number, hint = "") {
  const n = c.arguments.length;
  if (n < min || n > max) {
    const want = min === max ? `${min}` : `${min}–${max}`;
    fail(c, `${what} takes ${want} argument${max === 1 ? "" : "s"} in VTS, got ${n}${hint ? ` (${hint})` : ""}`);
  }
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
  const w = widen(v, expected, env);
  if (w) return w;
  if (expected.k === "void" || expected.k === "unit") return v;
  fail(node, `type mismatch: expected ${showType(expected)}, got ${showType(v.type)}`);
}

/**
 * The value `v` at a wider type `t` (the same JS value): an int as a number, a present value as
 * an optional one, an array elementwise (`int[]` as `(int | null)[]`, as TypeScript allows for
 * readonly arrays).  null when `t` is not wider.
 */
function widen(v: Val, t: VType, env: Env): Val | null {
  if (sameType(v.type, t)) return v;
  if (t.k === "num" && v.type.k === "int") return { code: `(VReact.JS.Num.ofInt ${paren(v.code)})`, type: T.num };
  // a string-literal enum member is its string (the `ToJS` instance of the enum maps each
  // constructor to its literal)
  if (t.k === "str" && v.type.k === "enum") return { code: `(VReact.JS.str ${paren(v.code)})`, type: T.str };
  if (t.k === "opt" && v.type.k !== "opt") {
    const w = widen(v, t.elem, env);
    return w && { code: `(some ${paren(w.code)})`, type: t };
  }
  if (t.k === "arr" && v.type.k === "arr") {
    if (v.code === "[]") return { code: "[]", type: t };
    const x = env.m.fresh("x");
    const w = widen({ code: x, type: v.type.elem }, t.elem, env);
    return w && { code: `(List.map (fun (${x} : ${leanType(v.type.elem)}) => ${w.code}) ${paren(v.code)})`, type: t };
  }
  return null;
}

/* ───────────────────────────── expressions ───────────────────────────── */

export function expr(e: ts.Expression, env: Env, expected?: VType): Val {
  const v = expr0(e, env, expected);
  checkUncheckedValue(e, v, env);
  return coerce(v, expected, e, env);
}

function expr0(e: ts.Expression, env: Env, expected?: VType): Val {
  const m = env.m;
  // narrowed path? (a variant narrowing replaces a `some` one: `s: T | null` tested non-null,
  // then to be a variant, is that present value)
  const key = pathKey(env, e);
  if (key) {
    const n = env.narrow.get(key);
    if (n && (n.kind === "some" || n.kind === "variant")) return { code: n.code, type: n.type };
  }
  switch (e.kind) {
    case ts.SyntaxKind.ParenthesizedExpression:
      return expr((e as ts.ParenthesizedExpression).expression, env, expected);
    case ts.SyntaxKind.NumericLiteral: {
      // literals are always type-ascribed: a bare Lean numeral defaults to Nat (truncated subtraction)
      const text = (e as ts.NumericLiteral).text;
      if (expected?.k === "num" || /[.eE]/.test(text)) return { code: `(${text} : VReact.JS.Num)`, type: T.num };
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
      return { code: `(none : ${leanType(expected)})`, type: expected };
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
      if (!ty && hasNullLeaf(c)) {
        // `c ? x : null` (also nested: `c ? x : d ? y : null`): type a non-null leaf in its
        // (narrowed) environment, without emitting anything
        const ot = nonNullLeafType(c, env);
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
      if (inner.type.k !== "opt" && isPresentValue(inner.type)) return inner; // present (e.g. narrowed)
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
    return { code: `(none : ${leanType(expected)})`, type: expected };
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
    if (base.type.k !== "opt" && isPresentValue(base.type)) return fieldOf(base, name, pa, env); // present (e.g. narrowed)
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
    if (name === u.tag) return { code: `(${t.name}.${leanAccessor(name)} ${paren(base.code)})`, type: T.str };
    const sf = sharedFields(u.variants).find((f) => f.name === name);
    if (sf) return { code: `(${t.name}.${leanAccessor(name)} ${paren(base.code)})`, type: sf.type };
    const has = u.variants.filter((v) => v.fields.some((f) => f.name === name)).map((v) => `"${v.lit}"`);
    fail(node, `field ${name} is not present in every variant of ${showType(t)}${has.length ? ` (only in ${has.join(", ")})` : ""}: narrow first with a test on x.${u.tag} (if/else, early return, ?:, &&/||, switch) of this value — not through an alias (const isX = …) or \`in\`, and anew after reassigning a \`let\``);
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

/** The numeric part of an expected type (`int | null` → `int`), passed to operands of arithmetic. */
function numericExpected(expected?: VType): VType | undefined {
  const t = expected?.k === "opt" ? expected.elem : expected;
  return t && isNumeric(t) ? t : undefined;
}

function prefix(p: ts.PrefixUnaryExpression, env: Env, expected?: VType): Val {
  switch (p.operator) {
    case ts.SyntaxKind.ExclamationToken: {
      const v = expr(p.operand, env, T.bool);
      return { code: `(!${paren(v.code)})`, type: T.bool };
    }
    case ts.SyntaxKind.MinusToken: {
      if (ts.isNumericLiteral(p.operand)) {
        const v = expr(p.operand, env, numericExpected(expected));
        return { code: v.type.k === "int" ? leanInt(-BigInt(p.operand.text)) : `(-${v.code})`, type: v.type };
      }
      const v = expr(p.operand, env, numericExpected(expected));
      if (!isNumeric(v.type)) fail(p, "unary minus on a non-number");
      return { code: `(-${paren(v.code)})`, type: v.type };
    }
    case ts.SyntaxKind.PlusToken: {
      // `+x` is ToNumber(x): the identity on numbers only (`+"5"` is 5, `+true` is 1)
      const v = expr(p.operand, env, numericExpected(expected));
      if (!isNumeric(v.type)) fail(p, `unary + converts a ${showType(v.type)} to a number (ToNumber), which VTS does not model: only use it on numbers`);
      return v;
    }
    case ts.SyntaxKind.TildeToken:
      fail(p, BITWISE_MSG("~"));
    default:
      fail(p, "++/-- are only allowed as statements on local `let` variables");
  }
}

/** Bitwise operators: JS converts their operands to 32-bit integers (ToInt32), which VTS does not model. */
const BITWISE_MSG = (op: string) =>
  `the bitwise operator ${op} is not supported in VTS (JS applies it to the operands converted to 32-bit integers, which VTS does not model); use arithmetic (e.g. -x - 1 for ~x, Math.floor(x / 2) for x >> 1)`;
const BITWISE_OPS = new Set([
  ts.SyntaxKind.AmpersandToken, ts.SyntaxKind.BarToken, ts.SyntaxKind.CaretToken,
  ts.SyntaxKind.LessThanLessThanToken, ts.SyntaxKind.GreaterThanGreaterThanToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken,
  ts.SyntaxKind.AmpersandEqualsToken, ts.SyntaxKind.BarEqualsToken, ts.SyntaxKind.CaretEqualsToken,
  ts.SyntaxKind.LessThanLessThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
]);

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
    if (l.type.k !== "opt" && isPresentValue(l.type)) return l; // present (e.g. narrowed): the fallback is not evaluated
    if (l.type.k !== "opt") fail(b, "?? on a non-optional value");
    if (isNullLit(stripParens(b.right))) return l;
    // an optional fallback (`a ?? b ?? 0` is `(a ?? b) ?? 0`): the first present value
    let rt: VType | null = null;
    try {
      rt = typeOf(b.right, env);
    } catch {
      rt = null;
    }
    if (rt && rt.k === "opt" && sameType(rt, l.type)) {
      const r = expr(b.right, env, l.type);
      return { code: `(Option.or ${paren(l.code)} ${paren(r.code)})`, type: l.type };
    }
    const r = expr(b.right, env, l.type.elem);
    return { code: `(Option.getD ${paren(l.code)} ${paren(r.code)})`, type: l.type.elem };
  }
  if (op === K.EqualsToken || op === K.PlusEqualsToken || op === K.MinusEqualsToken) {
    fail(b, "assignments are statements in VTS (and only to local `let` variables)");
  }
  if (isEqOp(op) || isNeqOp(op)) {
    const neg = isNeqOp(op);
    const nt = nullTest(b, env);
    if (nt) {
      if (nt.isNull !== null) return { code: keepOperand(nt, nt.isNull !== neg ? "true" : "false"), type: T.bool };
      return { code: neg ? `(Option.isSome ${paren(nt.v.code)})` : `(Option.isNone ${paren(nt.v.code)})`, type: T.bool };
    }
    const { l, r } = eqOperands(b, env);
    // number equality is the opaque IEEE test (NaN !== NaN, 0 === -0)
    const eq = l.type.k === "num" ? `(VReact.JS.Num.eq ${paren(l.code)} ${paren(r.code)})` : `(VReact.JS.eq ${paren(l.code)} ${paren(r.code)})`;
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
    // numbers: the opaque comparisons of `VReact.JS.Num` (NaN compares false)
    const num = l.type.k === "num" || r.type.k === "num";
    if (num) {
      l = coerce(l, T.num, b, env);
      r = coerce(r, T.num, b, env);
    }
    const [a, bb] = fn[1] ? [r.code, l.code] : [l.code, r.code];
    return { code: `(VReact.JS.${num ? "Num." : ""}${fn[0]} ${paren(a)} ${paren(bb)})`, type: T.bool };
  }
  // arithmetic is computed at the numeric type; an optional expected type (`int | null`)
  // applies to the result only (expr() wraps it in `some`)
  if (op === K.PlusToken) {
    // string concatenation when an operand is a string (TypeScript's type of it decides, as the
    // value does in JS): the other operand is converted with ToString (exact on ints and booleans)
    if (isStringTyped(b.left, env) || isStringTyped(b.right, env)) {
      const l = expr(b.left, env);
      const r = expr(b.right, env);
      return { code: `(${concatPart(l, b.left, b)} ++ ${concatPart(r, b.right, b)})`, type: T.str };
    }
    const l = expr(b.left, env, numericExpected(expected));
    const r = expr(b.right, env, isNumeric(l.type) ? l.type : undefined);
    if (l.type.k === "str" || r.type.k === "str") {
      return { code: `(${concatPart(l, b.left, b)} ++ ${concatPart(r, b.right, b)})`, type: T.str };
    }
    return arith("+", l, r, b, env);
  }
  if (op === K.MinusToken || op === K.AsteriskToken) {
    const l = expr(b.left, env, numericExpected(expected));
    const r = expr(b.right, env, isNumeric(l.type) ? l.type : undefined);
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
  if (BITWISE_OPS.has(op)) fail(b, BITWISE_MSG(b.operatorToken.getText()));
  if (op >= K.FirstCompoundAssignment && op <= K.LastCompoundAssignment) {
    fail(b, `compound assignment ${b.operatorToken.getText()} is not supported in VTS (only x = e, x += e and x -= e, as statements on local \`let\` variables)`);
  }
  fail(b, `operator ${b.operatorToken.getText()} not supported in VTS`);
}

/**
 * A comparison with `null`/`undefined` (`x === null`, `x != undefined`, …): the tested optional
 * value, or `isNull` statically known (a present value: a narrowed path, `xs[i]`, `f(x)`, `x!`, …,
 * is not null), with `obs` telling whether evaluating the operand has obligations (its index,
 * precondition, non-null, … conditions: they stand, see `keepOperand`).  `null` if not such a test.
 */
function nullTest(b: ts.BinaryExpression, env: Env): { v: Val; isNull: boolean | null; obs: boolean } | null {
  const K = ts.SyntaxKind;
  const op = b.operatorToken.kind;
  if (op === K.EqualsEqualsToken || op === K.ExclamationEqualsToken) {
    if (!isNullLit(b.left) && !isNullLit(b.right)) fail(b, "use === / !== (loose equality is only allowed against null)");
  }
  if (!isNullLit(b.right) && !isNullLit(b.left)) return null;
  const lit = isNullLit(b.right) ? b.right : b.left;
  const other = isNullLit(b.right) ? b.left : b.right;
  const before = env.m.obCount();
  const v = expr(other, env);
  const obs = env.m.obCount() > before;
  if (v.type.k !== "opt") {
    // a present value (e.g. narrowed on this path) is never null/undefined
    if (isPresentValue(v.type)) return { v, isNull: false, obs };
    fail(b, "comparison with null/undefined of a non-optional value");
  }
  checkStrictNullTest(b, other, lit, op, env);
  return { v, isNull: null, obs };
}

/**
 * A statically decided null test (`result`: its Lean value, in code or as a proposition): JS still
 * evaluates the operand, so an operand with obligations is kept, bound and unused, for them.
 */
function keepOperand(nt: { v: Val; obs: boolean }, result: string): string {
  return nt.obs ? `(let _ := ${nt.v.code}; ${result})` : result;
}

/** VTS types whose JS values are never null or undefined (all but options and void). */
function isPresentValue(t: VType): boolean {
  return ["bool", "int", "num", "str", "enum", "rec", "union", "arr", "tuple"].includes(t.k);
}

/** The two operands of `===` / `!==` (not against null), at a common type JS compares by value. */
function eqOperands(b: ts.BinaryExpression, env: Env): { l: Val; r: Val } {
  const strLit = (e: ts.Expression) => ts.isStringLiteralLike(stripParens(e));
  let l = expr(b.left, env);
  // an enum member compared with a string literal: at the enum (a member constructor); with any
  // other string: as strings
  let r = l.type.k === "enum" && !strLit(b.right) ? expr(b.right, env) : expr(b.right, env, l.type.k === "enum" || l.type.k === "opt" ? l.type : undefined);
  if (l.type.k === "enum" && r.type.k === "str") l = coerce(l, T.str, b, env);
  if (l.type.k === "str" && r.type.k === "enum") {
    if (strLit(b.left)) l = expr(b.left, env, r.type);
    else r = coerce(r, T.str, b, env);
  }
  // `x.id === sel` with `sel: int | null`: compare as options (as for `sel === x.id`)
  if (r.type.k === "opt" && l.type.k !== "opt") {
    l = l.type.k === "str" && r.type.elem.k === "enum" ? expr(b.left, env, r.type) : coerce(l, r.type, b, env);
  }
  if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, b, env);
  if (r.type.k === "int" && l.type.k === "num") r = coerce(r, T.num, b, env);
  if (!sameType(l.type, r.type)) fail(b, `comparing ${showType(l.type)} with ${showType(r.type)}`);
  if (l.type.k !== "num" && !isPrimitiveEq(l.type)) {
    const t = l.type.k === "opt" ? l.type.elem : l.type;
    if (["rec", "arr", "union", "tuple"].includes(t.k)) fail(b, `=== on ${showType(l.type)} compares object identity in JS; compare keys/fields instead`);
    if (t.k === "num") fail(b, `=== on ${showType(l.type)} is not supported: narrow with !== null first, then compare the numbers`);
    fail(b, `=== is not supported on ${showType(l.type)}`);
  }
  if (l.type.k === "opt") checkOptionalEquality(b, b.left, b.right, env);
  return { l, r };
}

/** Is `e` a string (or string-literal enum) value according to TypeScript? */
function isStringTyped(e: ts.Expression, env: Env): boolean {
  const t = tsTypeOf(e, env);
  return !!t && (t.flags & ts.TypeFlags.StringLike) !== 0 || (!!t && t.isUnion() && t.types.every((p) => (p.flags & ts.TypeFlags.StringLike) !== 0));
}

/** An operand of a string concatenation `a + b`, as a string. */
function concatPart(v: Val, e: ts.Expression, node: ts.Node): string {
  if (v.type.k === "num") {
    fail(node, `\`+\` converts the number \`${nodeText(e, 30)}\` to a string with JS's Number::toString (shortest round-trip form), which VTS models only as an opaque function: use an int, or a template literal \`\${…}\` (where the conversion is opaque too)`);
  }
  if (v.type.k === "opt") fail(node, `\`${nodeText(e, 30)}\` may be null or undefined, which \`+\` would turn into the text "null" / "undefined": narrow it first`);
  return toStr(v, e);
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
      if (n && (n.kind === "some" || n.kind === "variant")) return coerce({ code: n.code, type: n.type }, t, p, env);
      const v = identifier(p.name, env, t, vs);
      checkUncheckedValue(p.name, v, env);
      return coerce(v, t, p, env);
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
  // ascribed, so that Lean never re-infers the element type (e.g. a fold over a literal)
  return { code: `(${code} : List ${leanType(elemT)})`, type: T.arr(elemT) };
}

/* ───────────────────────────── calls ───────────────────────────── */

/**
 * Translate an arrow function used as a pure lambda (array methods, contract lambdas), its
 * parameters of types `paramTypes`; `paramTs`: the TypeScript types of the values they receive
 * (their annotations are checked against them; by default against the contextual types).
 */
export function lambda(
  fn: ts.Expression,
  env: Env,
  paramTypes: VType[],
  expectedRet?: VType,
  paramTs?: readonly (ts.Type | null | undefined)[],
): { binders: string[]; typed: string[]; body: Val; obligations: boolean; env: Env } {
  if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) fail(fn, "expected an inline arrow function `(x) => …`");
  let e2 = env;
  const binders: string[] = [];
  const typed: string[] = [];
  fn.parameters.forEach((p, i) => {
    const t = paramTypes[i];
    if (!t) fail(p, "unexpected extra lambda parameter");
    if (p.dotDotDotToken || p.initializer || p.questionToken) fail(p, "rest, default and optional lambda parameters are not supported");
    const r = bindParam(p.name, t, e2, paramTs?.[i]);
    e2 = r.env;
    binders.push(r.binder);
    typed.push(`(${r.binder} : ${leanType(t)})`);
  });
  // JS passes every argument; a callback declaring fewer parameters ignores the rest
  for (let i = fn.parameters.length; i < paramTypes.length; i++) {
    binders.push("_");
    typed.push(`(_ : ${leanType(paramTypes[i])})`);
  }
  const before = env.m.obCount();
  const body = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, e2, expectedRet, fn) : expr(fn.body, e2, expectedRet);
  return { binders, typed, body, obligations: env.m.obCount() > before, env: e2 };
}

/**
 * Bind a parameter (identifier or object-destructuring pattern) to a fresh Lean variable of type
 * `t`.  For a parameter of a function expression, `realTs` is the TypeScript type of the value it
 * receives, against which its annotation is checked (`checkParamAnnotation`): by default the type
 * the function's context gives it; `"declared"` when the annotation itself is the parameter's
 * type (local helper closures: TypeScript checks every argument against it).
 */
export function bindParam(name: ts.BindingName, t: VType, env: Env, realTs?: ts.Type | null | "declared"): { env: Env; binder: string } {
  const p = name.parent;
  if (realTs !== "declared" && ts.isParameter(p) && (ts.isArrowFunction(p.parent) || ts.isFunctionExpression(p.parent))) {
    const fn = p.parent;
    const real = realTs !== undefined ? realTs : (contextualParamTsTypes(fn, env)?.[fn.parameters.indexOf(p)] ?? null);
    checkParamAnnotation(p, t, real, env);
  }
  if (ts.isIdentifier(name)) {
    const s = symbolOf(env, name)!;
    const { env: e2, name: ln } = freshLocal(env, leanIdent(name.text));
    // the real type of the value, for a parameter that TypeScript types `any` (see `tsTypeOf`)
    const known = realTs && realTs !== "declared" && !(realTs.flags & ts.TypeFlags.Any) ? realTs : undefined;
    return { env: bind(e2, s, { k: "val", code: ln, type: t, ...(known ? { ts: known } : {}) }), binder: ln };
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
    const r = bindParam(p.name, t, e2, "declared");
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
    // numbers: opaque (`Math.trunc` is not Lean's `Float.round`, nor any rounding Lean computes)
    return { code: `(VReact.JS.Num.${name} ${paren(v.code)})`, type: T.num };
  }
  if ((name === "round" || name === "ceil") && args.length === 1) {
    const v = expr(args[0], env);
    if (v.type.k === "int") return v;
    // `Math.round` rounds half-way cases towards +∞ (Lean's `Float.round` away from zero, and
    // `floor(x + 0.5)` is wrong for 0.49999999999999994 and -0.5): opaque
    return { code: `(VReact.JS.Num.${name} ${paren(v.code)})`, type: T.num };
  }
  if ((name === "max" || name === "min") && args.length >= 2) {
    let vs = args.map((a) => expr(a, env, expected?.k === "num" ? T.num : undefined));
    const anyNum = vs.some((v) => v.type.k === "num");
    if (anyNum) vs = vs.map((v, i) => coerce(v, T.num, args[i], env));
    // on numbers the opaque `Math.max`/`Math.min` (NaN if any argument is NaN, +0 above -0; Lean's
    // `max` on Float is `maxOfLe`); folding the binary one is the n-ary one
    const fn = anyNum ? `VReact.JS.Num.${name}` : name;
    let code = vs[0].code;
    for (const v of vs.slice(1)) code = `(${fn} ${paren(code)} ${paren(v.code)})`;
    return { code, type: anyNum ? T.num : T.int };
  }
  if (name === "abs" && args.length === 1) {
    const v = expr(args[0], env);
    return v.type.k === "int" ? { code: `(VReact.JS.abs ${paren(v.code)})`, type: T.int } : { code: `(VReact.JS.Num.abs ${paren(v.code)})`, type: T.num };
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

/**
 * The callback over `xs.attach` binding the element `x` and its membership proof `h`, as
 * projections of a typed binder.  Not `fun ⟨x, h⟩ => body`: that is a `match`, whose
 * alternative stays a delayed-assigned metavariable until every obligation inside it is
 * solved, so an obligation Lean runs first (the enclosing handler's) would see the whole
 * callback as an opaque `?m x`.  (`have`: the membership is an ordinary hypothesis of
 * the obligations inside, which the automation normalises.)
 */
function attachLam(m: ModCtx, x: string, h: string, elem: VType, body: string): string {
  const p = m.fresh("p");
  const t = leanType(elem);
  return `(fun (${p} : {${m.fresh("y")} : ${t} // _}) => let ${x} : ${t} := ${p}.1; have ${h} := ${p}.2; ${body})`;
}

function arrayMethod(name: string, xs: Val, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const args = c.arguments;
  const m = env.m;
  const elem = (xs.type as { elem: VType }).elem;
  const X = paren(xs.code);
  // the TypeScript type of the elements (callback parameter annotations are checked against it)
  const elT = elemTsType((c.expression as ts.PropertyAccessExpression).expression, env) ?? undefined;
  const numT = m.checker.getNumberType();
  const withAttach = (args0: ts.Expression, paramTypes: VType[], ret: VType | undefined) => {
    const lam = lambda(args0, env, paramTypes, ret, [elT]);
    return lam;
  };
  // every modelled method has an exact arity: optional JS arguments that are not modelled
  // (thisArg, fromIndex, …) are rejected rather than ignored
  const callbackArity = () => arity(c, name, 1, 1, "a thisArg argument is not supported");
  switch (name) {
    case "map": {
      callbackArity();
      const fn = args[0];
      if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) fail(fn, "map needs an inline arrow function");
      if (fn.parameters.length === 2) {
        const lam = lambda(fn, env, [elem, T.int], expected?.k === "arr" ? expected.elem : undefined, [elT, numT]);
        if (lam.obligations) fail(fn, "map with an index parameter cannot contain proof obligations; precompute with a helper");
        const [x, i] = lam.binders;
        // the Nat index is bound to a subscripted name (never a VTS identifier), then as the Int `i`
        const k = "idx₀";
        return { code: `(${X}.zipIdx.map (fun (${x}, ${k}) => let ${i} : Int := ${k}; ${lam.body.code}))`, type: T.arr(lam.body.type) };
      }
      const lam = withAttach(fn, [elem], expected?.k === "arr" ? expected.elem : undefined);
      if (lam.obligations) {
        const h = m.fresh("hmem");
        return { code: `(${X}.attach.map ${attachLam(m, lam.binders[0], h, elem, lam.body.code)})`, type: T.arr(lam.body.type) };
      }
      return { code: `(${X}.map ${lamCode(lam.typed, lam.body.code)})`, type: T.arr(lam.body.type) };
    }
    case "filter":
    case "some":
    case "every":
    case "find": {
      callbackArity();
      if (name === "find" && elem.k === "opt") fail(c, "find on an array of optional values is not supported (a found null and \"not found\" (undefined) would be conflated)");
      const lam = withAttach(args[0], [elem], T.bool);
      const lean = { filter: "filter", some: "any", every: "all", find: "find?" }[name];
      const rt = name === "filter" ? xs.type : name === "find" ? T.opt(elem) : T.bool;
      if (lam.obligations) {
        const h = m.fresh("hmem");
        const core = `(${X}.attach.${lean} ${attachLam(m, lam.binders[0], h, elem, lam.body.code)})`;
        if (name === "filter") return { code: `(${core}.map (·.1))`, type: rt };
        if (name === "find") return { code: `(${core}.map (·.1))`, type: rt };
        return { code: core, type: rt };
      }
      return { code: `(${X}.${lean} ${lamCode(lam.typed, lam.body.code)})`, type: rt };
    }
    case "findIndex": {
      callbackArity();
      const lam = lambda(args[0], env, [elem], T.bool, [elT]);
      if (lam.obligations) fail(args[0], "findIndex predicates cannot contain proof obligations");
      return { code: `(VReact.JS.findIndex ${X} ${lamCode(lam.typed, lam.body.code)})`, type: T.int };
    }
    case "includes": {
      arity(c, "includes", 1, 1, "a fromIndex is not supported: write xs.slice(k).includes(v)");
      checkPrimitiveElems(c, (c.expression as ts.PropertyAccessExpression).expression, elem, "includes", env);
      const v = expr(args[0], env, elem);
      return { code: `(${X}.contains ${paren(v.code)})`, type: T.bool };
    }
    case "indexOf": {
      arity(c, "indexOf", 1, 1, "a fromIndex is not supported");
      checkPrimitiveElems(c, (c.expression as ts.PropertyAccessExpression).expression, elem, "indexOf", env);
      const v = expr(args[0], env, elem);
      return { code: `(VReact.JS.indexOf ${X} ${paren(v.code)})`, type: T.int };
    }
    case "slice": {
      arity(c, "slice", 0, 2);
      const a = args[0] ? expr(args[0], env, T.int).code : leanInt(0);
      const b = args[1] ? ` (some ${paren(expr(args[1], env, T.int).code)})` : "";
      return { code: `(VReact.JS.slice ${X} ${paren(a)}${b})`, type: xs.type };
    }
    case "concat": {
      // (every argument must be an array of the same type: JS would append a non-array as an element)
      const parts = args.map((a) => paren(expr(a, env, xs.type).code));
      return { code: `(${[X, ...parts].join(" ++ ")})`, type: xs.type };
    }
    case "join": {
      arity(c, "join", 0, 1);
      if (elem.k !== "str") fail(c, "join is supported on string arrays (map to strings first)");
      const sep = args[0] ? expr(args[0], env, T.str).code : jsStr(",");
      return { code: `(VReact.JS.join ${X} ${paren(sep)})`, type: T.str };
    }
    case "reduce": {
      if (args.length !== 2) fail(c, "reduce needs an initial value");
      const init = expr(args[1], env, expected);
      // (the accumulator's annotation is the type TypeScript checks every accumulated value against)
      const lam = lambda(args[0], env, [init.type, elem], init.type, [undefined, elT]);
      if (lam.obligations) fail(args[0], "reduce callbacks cannot contain proof obligations");
      return { code: `(${X}.foldl ${lamCode(lam.typed, lam.body.code)} ${paren(init.code)})`, type: init.type };
    }
    case "toSorted": {
      if (!args[0]) fail(c, "toSorted needs a comparator (a, b) => number");
      arity(c, "toSorted", 1, 1);
      if (elem.k === "opt") {
        // JS moves `undefined` elements to the end without calling the comparator
        const et = ts.isPropertyAccessExpression(c.expression) ? elemTsType(c.expression.expression, env) : null;
        const k = et ? kindsOfType(et) : null;
        if (!k || k.undef)
          fail(c, "toSorted on an array that may contain undefined is not supported (JS sorts undefined to the end without calling the comparator); filter or map the elements to a defined type first");
      }
      const lam = lambda(args[0], env, [elem, elem], T.int, [elT, elT]);
      if (lam.obligations) fail(args[0], "comparators cannot contain proof obligations");
      if (lam.body.type.k !== "int") fail(args[0], "comparator must return an int");
      return { code: `(VReact.JS.toSorted ${X} ${lamCode(lam.typed, lam.body.code)})`, type: xs.type };
    }
    case "toReversed":
      arity(c, "toReversed", 0, 0);
      return { code: `(${X}.reverse)`, type: xs.type };
    case "with": {
      arity(c, "with", 2, 2);
      const i = expr(args[0], env, T.int);
      const v = expr(args[1], env, elem);
      const ob = m.ob(c, "index", `index ${nodeText(args[0])} is within bounds for .with`);
      return { code: `(VReact.JS.withAt ${X} ${paren(i.code)} ${paren(v.code)} ${ob})`, type: xs.type };
    }
    case "at": {
      arity(c, "at", 1, 1);
      if (elem.k === "opt") fail(c, "at on an array of optional values is not supported (a null element and \"out of range\" (undefined) would be conflated)");
      const i = expr(args[0], env, T.int);
      return { code: `(VReact.JS.atOpt ${X} ${paren(i.code)})`, type: T.opt(elem) };
    }
    case "flatMap": {
      callbackArity();
      const lam = lambda(args[0], env, [elem], expected, [elT]);
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
      arity(c, "trim", 0, 0);
      return { code: `(VReact.JS.trim ${S})`, type: T.str };
    case "toLowerCase":
      arity(c, "toLowerCase", 0, 0);
      return { code: `(VReact.JS.toLowerCase ${S})`, type: T.str };
    case "toUpperCase":
      arity(c, "toUpperCase", 0, 0);
      return { code: `(VReact.JS.toUpperCase ${S})`, type: T.str };
    case "includes":
      arity(c, "includes", 1, 1, "a position is not supported: for p >= 0 write s.slice(p).includes(t)");
      return { code: `(VReact.JS.strIncludes ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "startsWith":
      arity(c, "startsWith", 1, 1, "a position is not supported: for p >= 0 write s.slice(p).startsWith(t)");
      return { code: `(VReact.JS.startsWith ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "endsWith":
      arity(c, "endsWith", 1, 1, "an end position is not supported: for e >= 0 write s.slice(0, e).endsWith(t)");
      return { code: `(VReact.JS.endsWith ${S} ${paren(expr(args[0], env, T.str).code)})`, type: T.bool };
    case "slice": {
      arity(c, "slice", 0, 2);
      const a = args[0] ? expr(args[0], env, T.int).code : leanInt(0);
      const b = args[1] ? ` (some ${paren(expr(args[1], env, T.int).code)})` : "";
      return { code: `(VReact.JS.strSlice ${S} ${paren(a)}${b})`, type: T.str };
    }
    case "repeat": {
      arity(c, "repeat", 1, 1);
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
      arity(c, name, 3, 3);
      const lo = expr(args[0], env, T.int);
      const hi = expr(args[1], env, T.int);
      const lam = lambda(args[2], env, [T.int], T.bool, [env.m.checker.getNumberType()]);
      const op = name === "forall" ? "all" : "any";
      const R = `(VReact.JS.rangeFrom ${paren(lo.code)} ${paren(hi.code)})`;
      if (lam.obligations) {
        // the body's obligations may use the bounds of i (membership in the range)
        const h = env.m.fresh("hmem");
        return { code: `(${R}.attach.${op} ${attachLam(env.m, lam.binders[0], h, T.int, lam.body.code)})`, type: T.bool };
      }
      return { code: `(${R}.${op} ${lamCode(lam.typed, lam.body.code)})`, type: T.bool };
    }
    case "distinct": {
      arity(c, "distinct", 1, 2);
      const xs = expr(args[0], env);
      if (xs.type.k !== "arr") fail(c, "distinct expects an array");
      if (args[1]) {
        const lam = lambda(args[1], env, [xs.type.elem], undefined, [elemTsType(args[0], env) ?? undefined]);
        checkDistinctKey(c, lam.body.type);
        return { code: `(VReact.JS.nodupB (${paren(xs.code)}.map ${lamCode(lam.typed, lam.body.code)}))`, type: T.bool };
      }
      checkPrimitiveElems(c, args[0], xs.type.elem, "distinct (without a key function)", env);
      return { code: `(VReact.JS.nodupB ${paren(xs.code)})`, type: T.bool };
    }
    case "implies": {
      // a function call: JS evaluates both arguments (in code; contracts read it as an implication)
      arity(c, "implies", 2, 2);
      const a = expr(args[0], env, T.bool);
      const b = expr(args[1], env, T.bool);
      return { code: `((!${paren(a.code)}) || ${paren(b.code)})`, type: T.bool };
    }
    case "idiv": {
      arity(c, "idiv", 2, 2);
      const a = expr(args[0], env, T.int);
      const b = expr(args[1], env, T.int);
      const ob = env.m.ob(c, "nonzero-divisor", `divisor ${nodeText(args[1])} is non-zero`);
      return { code: `(VReact.JS.floorDiv ${paren(a.code)} ${paren(b.code)} ${ob})`, type: T.int };
    }
    case "range": {
      arity(c, "range", 1, 1);
      const n = expr(args[0], env, T.int);
      return { code: `(VReact.JS.range ${paren(n.code)})`, type: T.arr(T.int) };
    }
    case "hole": {
      // an unfilled synthesis placeholder: translated as `sorry` (reported INCOMPLETE)
      const t = c.typeArguments?.[0] ? typeOfNode(c.typeArguments[0], env.m.prog.typeEnv, "Hole") : undefined;
      if (!t) fail(c, "write hole<T>() with an explicit type");
      // vreact synth types its candidates with the narrowing in effect here
      if (!env.m.dry) env.m.prog.holeEnvs?.push({ node: c, env });
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
      const key = pathKey(env, target);
      if (!key) return null;
      if (env.narrow.get(key)?.kind !== "some") checkStrictNullTest(e, target, isNullLit(e.right) ? e.right : e.left, k, env);
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
  d.dry = true;
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
    // an object known to be non-null (narrowed) is truthy
    if (t && ["rec", "arr", "union", "tuple"].includes(t.k) && narrowedSome(env, e)) return onTrue(env);
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
  const key = pathKey(env, nt.target)!;
  const target = expr(nt.target, env);
  // a present (e.g. already narrowed) value is not null: the test is decided
  if (nt.kind === "null" && target.type.k !== "opt" && isPresentValue(target.type)) return (nt.positive ? onFalse : onTrue)(env);
  const h = env.m.fresh("h");
  if (nt.kind === "null") {
    // already narrowed to non-null (an enclosing test, or `x = e` with a non-null e): decided statically
    if (narrowedSome(env, nt.target)) return nt.positive ? onFalse(env) : onTrue(env);
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
  // already narrowed to one variant (an enclosing test or switch arm): decided statically
  const known = env.narrow.get(key);
  if (known && known.kind === "variant") return (known.variant === variant.lit) === nt.positive ? onTrue(env) : onFalse(env);
  const ut = target.type;
  /** a match pattern for variant `v`, and `env` narrowed to it (its fields bound) */
  const arm = (v: Variant): { pat: string; env: Env } => {
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
    narrow.set(key, { kind: "variant", code: target.code, type: ut, variant: v.lit, fields });
    return { pat: `.${leanField(v.ctor)}${names.map((n) => " " + n).join("")}`, env: { ...e1, narrow } };
  };
  const whenIs = nt.positive ? onTrue : onFalse;
  const whenNot = nt.positive ? onFalse : onTrue;
  const yesArm = arm(variant);
  let arms = `\n  | ${yesArm.pat} => ${paren(whenIs(yesArm.env))}`;
  const others = u.variants.filter((v) => v !== variant);
  if (others.length === 1) {
    // the complement is a single variant: narrow to it (else branch, early return, `||`, ternary)
    const a = arm(others[0]);
    arms += `\n  | ${a.pat} => ${paren(whenNot(a.env))}`;
  } else if (others.length > 1) {
    // several variants remain: one arm, unless the code there needs to know which one
    // (a later test excludes all but one); then one arm per remaining variant
    const m = env.m;
    const nObs = m.obligations.length;
    const nCount = m.counter.n;
    const nHoles = m.prog.holeEnvs?.length ?? 0;
    // (vreact synth only: which variants are left in the `_` arm; the term is the same)
    let restEnv = env;
    if (m.prog.holeEnvs) {
      const before = env.remaining?.get(key);
      const remaining = new Map(env.remaining ?? []);
      remaining.set(key, others.map((v) => v.lit).filter((l) => !before || before.includes(l)));
      restEnv = { ...env, remaining };
    }
    try {
      arms += `\n  | _ => ${paren(whenNot(restEnv))}`;
    } catch (err) {
      if (!(err instanceof VtsError)) throw err;
      m.obligations.length = nObs;
      m.counter.n = nCount;
      if (m.prog.holeEnvs) m.prog.holeEnvs.length = nHoles;
      for (const v of others) {
        const a = arm(v);
        arms += `\n  | ${a.pat} => ${paren(whenNot(a.env))}`;
      }
    }
  }
  return `(match ${h} : ${target.code} with${arms})`;
}

/**
 * A VTS boolean expression as a Lean proposition (used for contracts:
 * requires / invariant / ensures / callbackRequires / assert).  Connectives,
 * comparisons and quantifying array methods become logical connectives and
 * quantifiers, so that automation never sees `decide` instances in specs.
 *
 * Guards are in scope where JS evaluates under them: the right operand of `&&`
 * (`||`) under a hypothesis that the left one holds (fails), the branches of
 * `?:` and the consequent of `implies(a, b)` under the condition, a quantifier
 * body under its bounds / membership.  When the guarded part has no proof
 * obligations the plain connective is emitted (`∧`, `∨`, `→`: same normal forms);
 * otherwise a named hypothesis binds the guard (`∃ (h : a), b`, `∀ (h : a), b`).
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
    if (op === K.AmpersandAmpersandToken) return propAnd(e.left, env, (e1) => prop(e.right, e1));
    if (op === K.BarBarToken) return propGuarded(e.left, env, "or", (e2) => prop(e.right, e2));
    const nt = narrowTest(e, env);
    if (nt) return propNarrow(nt, env, () => "True", () => "False");
    if (isEqOp(op) || isNeqOp(op)) {
      const nl = nullTest(e, env);
      if (nl) {
        if (nl.isNull !== null) return keepOperand(nl, nl.isNull !== isNeqOp(op) ? "True" : "False");
        return `((${isNeqOp(op) ? "Option.isSome" : "Option.isNone"} ${paren(nl.v.code)}) = true)`;
      }
      const { l, r } = eqOperands(e, env);
      // number equality is IEEE (NaN !== NaN), exactly as in code: the opaque test; Lean's `=`
      // would be reflexive
      if (l.type.k === "num") return `((VReact.JS.Num.eq ${paren(l.code)} ${paren(r.code)}) = ${isNeqOp(op) ? "false" : "true"})`;
      return `(${l.code} ${isNeqOp(op) ? "≠" : "="} ${r.code})`;
    }
    const cmp: Record<number, string> = { [K.LessThanToken]: "<", [K.LessThanEqualsToken]: "≤", [K.GreaterThanToken]: ">", [K.GreaterThanEqualsToken]: "≥" };
    if (cmp[op]) {
      let l = expr(e.left, env);
      let r = expr(e.right, env, l.type);
      if (l.type.k === "int" && r.type.k === "num") l = coerce(l, T.num, e, env);
      if (!isNumeric(l.type)) fail(e, "ordering comparison on non-numbers");
      if (l.type.k === "num" || r.type.k === "num") {
        // numbers: the opaque comparisons (NaN compares false)
        l = coerce(l, T.num, e, env);
        r = coerce(r, T.num, e, env);
        const [f, a, bb] = ({ "<": ["lt", l, r], "≤": ["le", l, r], ">": ["lt", r, l], "≥": ["le", r, l] } as Record<string, [string, Val, Val]>)[cmp[op]];
        return `((VReact.JS.Num.${f} ${paren(a.code)} ${paren(bb.code)}) = true)`;
      }
      return `(${l.code} ${cmp[op]} ${r.code})`;
    }
  }
  if (ts.isConditionalExpression(e)) {
    const nt = narrowTest(e.condition, env);
    if (nt) return propNarrow(nt, env, (e1) => prop(e.whenTrue, e1), (e2) => prop(e.whenFalse, e2));
    return retryNarrowed(
      e.condition,
      env,
      () => {
        const c = prop(e.condition, env);
        return `((∀ (${env.m.fresh("h")} : ${c}), ${prop(e.whenTrue, env)}) ∧ (∀ (${env.m.fresh("h")} : ¬${paren(c)}), ${prop(e.whenFalse, env)}))`;
      },
      () => `(${guard(e.condition, true, "imp", env, (e1) => prop(e.whenTrue, e1))} ∧ ${guard(e.condition, false, "imp", env, (e2) => prop(e.whenFalse, e2))})`,
    );
  }
  if (ts.isCallExpression(e)) {
    const sf = specFn(env, e.expression);
    const args = e.arguments;
    if (sf === "implies") {
      arity(e, "implies", 2, 2);
      return propGuarded(args[0], env, "imp", (e1) => prop(args[1], e1));
    }
    if (sf === "forall" || sf === "exists") {
      arity(e, sf, 3, 3);
      const lo = expr(args[0], env, T.int);
      const hi = expr(args[1], env, T.int);
      const fn = args[2];
      if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length !== 1) fail(e, `${sf}(lo, hi, (i) => …)`);
      const r = bindParam(fn.parameters[0].name, T.int, env, env.m.checker.getNumberType());
      if (ts.isBlock(fn.body)) fail(fn.body, "quantifier body must be an expression");
      const i = r.binder;
      const before = env.m.obCount();
      const body = prop(fn.body, r.env);
      const guarded = env.m.obCount() > before;
      if (sf === "forall") {
        if (!guarded) return `(∀ ${i} : Int, ${paren(lo.code)} ≤ ${i} → ${i} < ${paren(hi.code)} → ${body})`;
        return `(∀ ${i} : Int, ∀ (${env.m.fresh("h")} : ${paren(lo.code)} ≤ ${i}), ∀ (${env.m.fresh("h")} : ${i} < ${paren(hi.code)}), ${body})`;
      }
      return guarded
        ? `(∃ ${i} : Int, ∃ (${env.m.fresh("h")} : ${paren(lo.code)} ≤ ${i} ∧ ${i} < ${paren(hi.code)}), ${body})`
        : `(∃ ${i} : Int, ${paren(lo.code)} ≤ ${i} ∧ ${i} < ${paren(hi.code)} ∧ ${body})`;
    }
    if (sf === "distinct") {
      arity(e, "distinct", 1, 2);
      const xs = expr(args[0], env);
      if (xs.type.k !== "arr") fail(e, "distinct expects an array");
      if (!args[1]) {
        checkPrimitiveElems(e, args[0], xs.type.elem, "distinct (without a key function)", env);
        return `(${paren(xs.code)}.Nodup)`;
      }
      const lam = lambda(args[1], env, [xs.type.elem], undefined, [elemTsType(args[0], env) ?? undefined]);
      checkDistinctKey(e, lam.body.type);
      return `((${paren(xs.code)}.map ${lamCode(lam.typed, lam.body.code)}).Nodup)`;
    }
    if (ts.isPropertyAccessExpression(e.expression) && ["every", "some", "includes"].includes(e.expression.name.text)) {
      const xs = expr(e.expression.expression, env);
      if (xs.type.k === "arr") {
        const mname = e.expression.name.text;
        if (mname === "includes") {
          arity(e, "includes", 1, 1, "a fromIndex is not supported: write xs.slice(k).includes(v)");
          checkPrimitiveElems(e, e.expression.expression, xs.type.elem, "includes", env);
          return `(${expr(args[0], env, xs.type.elem).code} ∈ ${paren(xs.code)})`;
        }
        arity(e, mname, 1, 1, "a thisArg argument is not supported");
        const fn = args[0];
        if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length !== 1 || ts.isBlock(fn.body)) {
          fail(e, `${mname}((x) => condition) with an expression body`);
        }
        const r = bindParam(fn.parameters[0].name, xs.type.elem, env, elemTsType(e.expression.expression, env) ?? undefined);
        const before = env.m.obCount();
        const body = prop(fn.body as ts.Expression, r.env);
        const x = r.binder;
        if (env.m.obCount() === before) return mname === "every" ? `(∀ ${x} ∈ ${paren(xs.code)}, ${body})` : `(∃ ${x} ∈ ${paren(xs.code)}, ${body})`;
        const hm = env.m.fresh("hmem");
        return mname === "every"
          ? `(∀ ${x}, ∀ (${hm} : ${x} ∈ ${paren(xs.code)}), ${body})`
          : `(∃ ${x}, ∃ (${hm} : ${x} ∈ ${paren(xs.code)}), ${body})`;
      }
    }
  }
  const v = expr(e, env, T.bool);
  return `(${paren(v.code)} = true)`;
}

/**
 * `left && right` as a proposition, `right` built (by `rightK`) under the guard `left`:
 * narrowing (`x !== null && P(x)`), or a named hypothesis when `right` has obligations.
 */
function propAnd(left: ts.Expression, env: Env, rightK: (e: Env) => string): string {
  return propGuarded(left, env, "and", rightK);
}

/**
 * `left && right` ("and"), `left || right` ("or") or `implies(left, right)` ("imp")
 * as a proposition, `right` built by `rightK` where JS evaluates it: under `left`
 * ("and", "imp") or under its failure ("or") — narrowed as `branch` narrows code,
 * also by a compound `left` (`b || s.kind === "a" || s.to …`, `x !== null &&
 * y !== null && x + y …`, `!(p === null || q === null) || …`).  A compound `left` is
 * first read as one condition (the usual normal form); only when `right` needs
 * its narrowing is it decomposed (`guard`).  Both mean the same.
 */
function propGuarded(left: ts.Expression, env: Env, conn: "and" | "or" | "imp", rightK: (e: Env) => string): string {
  const nt = narrowTest(left, env);
  if (nt) {
    if (conn === "and") return propNarrow(nt, env, rightK, () => "False");
    if (conn === "imp") return propNarrow(nt, env, rightK, () => "True");
    return propNarrow(nt, env, () => "True", rightK);
  }
  return retryNarrowed(left, env, () => guardAtom(prop(left, env), conn !== "or", conn === "and" ? "and" : "imp", env, rightK), () => guard(left, conn !== "or", conn === "and" ? "and" : "imp", env, rightK));
}

/**
 * `whole()`, unless `c` is a compound condition with narrowing tests and `whole()`
 * is rejected (a later operand needs the narrowing): then `parts()`.  The
 * obligations of the abandoned attempt are withdrawn.
 */
function retryNarrowed(c: ts.Expression, env: Env, whole: () => string, parts: () => string): string {
  const c0 = stripParens(c);
  const compound = (ts.isPrefixUnaryExpression(c0) && c0.operator === ts.SyntaxKind.ExclamationToken) ||
    (ts.isBinaryExpression(c0) && [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken].includes(c0.operatorToken.kind));
  if (!compound || !hasNarrowing(c0, env)) return whole();
  const m = env.m;
  const nObs = m.obligations.length;
  const nCount = m.counter.n;
  try {
    return whole();
  } catch (err) {
    if (!(err instanceof VtsError)) throw err;
    m.obligations.length = nObs;
    m.counter.n = nCount;
    return parts();
  }
}

/**
 * The proposition "c is `pos`, and (`mode` "and") / then (`mode` "imp") K", where K
 * (`k`) is built in the environment narrowed by c being `pos` — `branch`'s
 * decomposition: `!x` flips; `a && b` true and `a || b` false are both parts in
 * turn (`a ∧ (b ∧ K)`, `a ∨ (b ∨ K)`); `a && b` false and `a || b` true narrow
 * nothing (either part may be the reason) and stay one condition.
 */
function guard(c: ts.Expression, pos: boolean, mode: "and" | "imp", env: Env, k: (e: Env) => string): string {
  const e = stripParens(c);
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) return guard(e.operand, !pos, mode, env, k);
  if (ts.isBinaryExpression(e) && hasNarrowing(e, env)) {
    const op = e.operatorToken.kind;
    if ((op === ts.SyntaxKind.AmpersandAmpersandToken && pos) || (op === ts.SyntaxKind.BarBarToken && !pos)) {
      return guard(e.left, pos, mode, env, (e1) => guard(e.right, pos, mode, e1, k));
    }
  }
  const nt = narrowTest(e, env);
  if (nt) {
    const otherwise = () => (mode === "and" ? "False" : "True");
    return pos ? propNarrow(nt, env, k, otherwise) : propNarrow(nt, env, otherwise, k);
  }
  return guardAtom(prop(e, env), pos, mode, env, k);
}

/**
 * `l` (a proposition) is `pos`, and/then `k(env)`: `l ∧ K`, `¬l ∧ K`, `∀ (h : l), K`,
 * `l ∨ K` — with a named hypothesis (`∃ (h : …), K`, `l ∨ ∃ (h : ¬l), K`) when K has
 * obligations that may need it.
 */
function guardAtom(l: string, pos: boolean, mode: "and" | "imp", env: Env, k: (e: Env) => string): string {
  const before = env.m.obCount();
  const r = k(env);
  const plain = env.m.obCount() === before;
  if (mode === "and") {
    const lp = pos ? l : `¬${paren(l)}`;
    return plain ? `(${lp} ∧ ${r})` : `(∃ (${env.m.fresh("h")} : ${lp}), ${r})`;
  }
  if (pos) return `(∀ (${env.m.fresh("h")} : ${l}), ${r})`;
  return plain ? `(${l} ∨ ${r})` : `(${l} ∨ ∃ (${env.m.fresh("h")} : ¬${paren(l)}), ${r})`;
}

/** Several conditions (`requires(a); requires(b)`) as one proposition, each guarded by the earlier ones. */
export function propAll(es: readonly ts.Expression[], env: Env): string {
  if (es.length === 0) return "True";
  if (es.length === 1) return prop(es[0], env);
  return propAnd(es[0], env, (e1) => propAll(es.slice(1), e1));
}

/** Narrowing inside propositions: `x !== null && P(x)` ↦ `match x with | some x => P x | none => False`. */
function propNarrow(nt: NarrowTest, env: Env, onTrue: (e: Env) => string, onFalse: (e: Env) => string): string {
  const s = narrowBranch(nt, env, onTrue, onFalse);
  // narrowBranch names the equation hypothesis (`h₁ : …`); drop it inside propositions
  return s.replace(/^\(match [^\s:]+ : /, "(match ");
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
  /** render: translate a JSX const at its declaration (`code`), of Lean type `type` */
  jsxConst?: { code: (e: ts.Expression, env: Env) => string; type: string };
  fnNode: ts.Node;
}

/** A value-returning block (function bodies, block-bodied lambdas). */
export function valueBlock(stmts: readonly ts.Statement[], env: Env, ret: VType | undefined, fnNode: ts.Node): Val {
  // the body of a top-level function: closures over its `let`s must agree with JS
  if (ts.isFunctionDeclaration(fnNode) && fnNode.body) checkClosures(fnNode.body, env);
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

/**
 * `const x = useMemo(…)` / `const f = useCallback(…)` declarations at the top level of a
 * component body, before any early return (registered by the component prepass).
 */
export const topLevelHookDecls = new WeakSet<ts.VariableDeclaration>();

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
  // useMemo / useCallback: only as top-level hook declarations of a component (Rules of Hooks:
  // React matches hooks by call order, so a hook in a branch, loop, handler or after an early
  // return reads another call's cached value or throws)
  if (ts.isCallExpression(init) && ["useMemo", "useCallback"].includes(hookName(env, init.expression) ?? "") && !topLevelHookDecls.has(d)) {
    fail(init, `hooks must be called at the top level of a component, unconditionally (Rules of Hooks)`);
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
  // JSX-valued const.  JS evaluates the element (its attribute and `{…}` child expressions)
  // here, at the declaration, whether or not it is rendered: so it is translated here, its
  // obligations under the facts of this point, and bound to a Lean local used at its uses.
  if (ts.isJsxElement(init) || ts.isJsxSelfClosingElement(init) || ts.isJsxFragment(init)) {
    if (!ts.isIdentifier(d.name)) fail(d, "destructuring JSX");
    const s = symbolOf(env, d.name)!;
    // the key function of a keyed map: the node function translates the same statements
    if (env.keyFn) return next(bind(env, s, { k: "jsx", node: init, env, code: "" }));
    if (bc.kind !== "render" || !bc.jsxConst) fail(init, "JSX is only allowed in a component's render (not in functions, handlers, effects or loops)");
    const code = bc.jsxConst.code(init, env);
    const { env: e1, name: ln } = freshLocal(env, leanIdent(d.name.text));
    return `(let ${ln} : ${bc.jsxConst.type} := ${code};\n${next(bind(e1, s, { k: "jsx", node: init, env, code: ln }))})`;
  }
  if (ts.isObjectBindingPattern(d.name)) {
    const v = expr(init, env, declT);
    const { env: e1, name: tmp } = freshLocal(env, "tmp");
    const r = bindParam(d.name, v.type, e1);
    // bindParam created its own local name; re-bind to tmp
    return `(let ${r.binder}${letType(v.type)} := ${v.code};\n${next(r.env)})`;
  }
  if (!ts.isIdentifier(d.name)) fail(d, "unsupported destructuring");
  const v = declT?.k === "opt" ? exprPreferElem(init, env, declT) : expr(init, env, declT);
  return bindLocal(d.name, v, env, next, declT);
}

/** ` : T` for a `let` (every local is type-ascribed, so Lean never re-infers, e.g. defaults to Nat). */
function letType(t: VType): string {
  try {
    return ` : ${leanType(t)}`;
  } catch {
    return "";
  }
}

/**
 * The value of `e` for an optional declared type `T | null`: at `T` when it is certainly
 * present (`x = 5`, `let x: int | null = 3`), so the local can be narrowed as TypeScript does.
 */
function exprPreferElem(e: ts.Expression, env: Env, t: VType & { k: "opt" }): Val {
  let rt: VType | null = null;
  try {
    rt = typeOf(e, env, t.elem);
  } catch {
    rt = null;
  }
  return rt && sameType(rt, t.elem) ? expr(e, env, t.elem) : expr(e, env, t);
}

/**
 * Bind a local.  A present value of an optional declared type binds the payload and narrows
 * the local (its option value is `some payload`).
 */
function bindLocal(name: ts.BindingName, v: Val, env: Env, next: (e: Env) => string, declT?: VType): string {
  if (!ts.isIdentifier(name)) fail(name, "unsupported binding");
  const s = symbolOf(env, name)!;
  const { env: e1, name: ln } = freshLocal(env, leanIdent(name.text));
  if (declT?.k === "opt" && v.type.k !== "opt" && sameType(v.type, declT.elem)) {
    const narrow = new Map(e1.narrow);
    narrow.set(`#${symId(s)}`, { kind: "some", code: ln, type: v.type });
    const e2 = bind({ ...e1, narrow }, s, { k: "val", code: `(some ${ln})`, type: declT });
    return `(let ${ln}${letType(v.type)} := ${v.code};\n${next(e2)})`;
  }
  const e2 = bind(e1, s, { k: "val", code: ln, type: v.type });
  return `(let ${ln}${letType(v.type)} := ${v.code};\n${next(e2)})`;
}

/** (alias used by the for-of translation) */
function dropNarrowing(env: Env, s: ts.Symbol): Env {
  return forgetNarrowing(env, s);
}

/** Forget what was known (narrowing) about a local and its property paths. */
function forgetNarrowing(env: Env, s: ts.Symbol): Env {
  const key = `#${symId(s)}`;
  const narrow = new Map([...env.narrow].filter(([k]) => k !== key && !k.startsWith(key + ".")));
  const remaining = env.remaining && new Map([...env.remaining].filter(([k]) => k !== key && !k.startsWith(key + ".")));
  return { ...env, narrow, remaining };
}

/**
 * Re-bind a mutable local after assignment.  `newVal(current, declared)`: `current` is the
 * current value (narrowed when known present), `declared` the local's declared type.
 */
function assignLocal(target: ts.Expression, newVal: (old: Val, declared: VType) => Val, env: Env, next: (e: Env) => string, node: ts.Node): string {
  if (!ts.isIdentifier(target)) fail(node, "only local `let` variables can be assigned (VTS data is immutable)");
  const s = symbolOf(env, target);
  const b = s ? env.vars.get(s) : undefined;
  if (!b || b.k !== "val") fail(node, `cannot assign to ${target.text}`);
  const decl = s!.valueDeclaration;
  if (!decl || !ts.isVariableDeclaration(decl) || !(decl.parent.flags & ts.NodeFlags.Let)) fail(node, `${target.text} is not a local let variable`);
  const known = env.narrow.get(`#${symId(s!)}`);
  const v = newVal(known?.kind === "some" ? { code: known.code, type: known.type } : { code: b.code, type: b.type }, b.type);
  // the old narrowing no longer describes the new value
  const { env: e1, name: ln } = freshLocal(forgetNarrowing(env, s!), leanIdent(target.text));
  if (b.type.k === "opt" && v.type.k !== "opt" && sameType(v.type, b.type.elem)) {
    // assignment narrowing (as in TypeScript): after `x = 5`, x is known to be present
    const narrow = new Map(e1.narrow);
    narrow.set(`#${symId(s!)}`, { kind: "some", code: ln, type: v.type });
    return `(let ${ln}${letType(v.type)} := ${v.code};\n${next(bind({ ...e1, narrow }, s!, { k: "val", code: `(some ${ln})`, type: b.type }))})`;
  }
  const c = coerce(v, b.type, node, env);
  return `(let ${ln}${letType(b.type)} := ${c.code};\n${next(bind(e1, s!, { k: "val", code: ln, type: b.type }))})`;
}

/**
 * The code after `assert(c)` / `assume(c)` (whose fact is the hypothesis `h`).  In a
 * handler, effect or timer body the outcome's own obligations (invariant
 * preservation, robustness, emits) are proved outside the body's term, where a
 * `have` is out of scope; so there the rest is guarded by the fact:
 * `if h' : c then rest else skip` (`type_of% h` is `c`, written once).  The
 * `else` is unreachable — `h` proves `c`, or `c` is assumed (`VReact.assumed`, still
 * in the term and reported) — and does nothing (no updates, no callback), so it
 * is safe for every obligation; splitting on the `if` gives them `h' : c`.
 */
function withFact(h: string, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  if (bc.kind !== "handler" || !env.handler || !env.comp) return rest(env);
  const skip = outcome({ ...env.handler, updates: [], emit: null }, env.comp);
  return `(open Classical in if ${env.m.fresh("hfact")} : type_of% ${h} then ${paren(rest(env))}\n  else ${skip})`;
}

function exprStatement(e: ts.Expression, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  const m = env.m;
  e = stripParens(e);
  // assignments
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (k === ts.SyntaxKind.EqualsToken) {
      if (ts.isPropertyAccessExpression(e.left) && e.left.getText() === "document.title") return rest(env); // external effect
      return assignLocal(e.left, (_old, declared) => (declared.k === "opt" ? exprPreferElem(e.right, env, declared) : expr(e.right, env, declared)), env, rest, e);
    }
    if (k === ts.SyntaxKind.PlusEqualsToken || k === ts.SyntaxKind.MinusEqualsToken) {
      const op = k === ts.SyntaxKind.PlusEqualsToken ? "+" : "-";
      return assignLocal(e.left, (old) => {
        const r = expr(e.right, env, isNumeric(old.type) ? old.type : undefined);
        if (old.type.k === "str" && op === "+") return { code: `(${old.code} ++ ${concatPart(r, e.right, e)})`, type: T.str };
        return arith(op, old, r, e, env);
      }, env, rest, e);
    }
    if (k >= ts.SyntaxKind.FirstCompoundAssignment && k <= ts.SyntaxKind.LastCompoundAssignment) {
      fail(e, BITWISE_OPS.has(k) ? BITWISE_MSG(e.operatorToken.getText()) : `compound assignment ${e.operatorToken.getText()} is not supported in VTS (only x = e, x += e and x -= e on local \`let\` variables): write x = x … e`);
    }
  }
  if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
    const op = e.operator === ts.SyntaxKind.PlusPlusToken ? "+" : "-";
    return assignLocal(e.operand, (old) => {
      if (!isNumeric(old.type)) fail(e, `++/-- on ${showType(old.type)}`);
      const one = old.type.k === "num" ? "(1 : VReact.JS.Num)" : leanInt(1);
      return { code: `(${old.code} ${op} ${one})`, type: old.type };
    }, env, rest, e);
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
        return `(have ${h} : ${p} := ${ob};\n${withFact(h, env, bc, rest)})`;
      }
      case "assume": {
        const p = prop(e.arguments[0], env);
        const h = m.fresh("hassume");
        return `(have ${h} : ${p} := VReact.assumed;\n${withFact(h, env, bc, rest)})`;
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
        const r = bindParam(p.name, t, e2, "declared");
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
  if (h.kind === "robust") fail(c, "parent callbacks cannot be invoked from effects, timers, continuous/default-priority events or onFocus/onBlur/onInvalid (robust handlers: they may run with a stale snapshot, or inside another event's batch)");
  if (h.emit) fail(c, "a handler may invoke at most one parent callback per execution path (otherwise the parent's updates would not be checked together)");
  const cb = comp.info.callbacks.find((x) => x.name === t.name)!;
  if (c.arguments.length !== cb.params.length) fail(c, `${cb.name} expects ${cb.params.length} arguments`);
  const as = c.arguments.map((a, i) => paren(expr(a, env, cb.params[i].type).code));
  const ob = m.ob(c, "callback-contract", `callback contract of ${cb.name}(${c.arguments.map((a) => nodeText(a, 30)).join(", ")})`);
  const emit = `(${comp.cbVar}.${leanField(cb.name)}${as.map((a) => " " + a).join("")} ${ob})`;
  return rest({ ...env, handler: { ...h, emit } });
}

/** A `case` label: `text` for a string literal, `key` for a literal (equal keys: equal JS values). */
interface CaseLabel {
  node: ts.Expression;
  text: string | null;
  key: string | null;
}

function caseLabel(e0: ts.Expression): CaseLabel {
  const e = stripParens(e0);
  if (ts.isStringLiteralLike(e)) return { node: e, text: e.text, key: `s:${JSON.stringify(e.text)}` };
  // (TypeScript normalises the text of a numeric literal to its value: 0x10 is "16", 1e2 "100")
  if (ts.isNumericLiteral(e)) return { node: e, text: null, key: `n:${String(Number(e.text))}` };
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(stripParens(e.operand))) {
    return { node: e, text: null, key: `n:${String(-Number((stripParens(e.operand) as ts.NumericLiteral).text))}` }; // (-0 is "0": 0 === -0)
  }
  if (e.kind === ts.SyntaxKind.TrueKeyword || e.kind === ts.SyntaxKind.FalseKeyword) return { node: e, text: null, key: `b:${e.kind === ts.SyntaxKind.TrueKeyword}` };
  return { node: e, text: null, key: null };
}

/**
 * The Lean test `disc === label` of a switch on a primitive value (JS compares with ===).  An
 * int discriminant never equals a non-integer number, so such a label is rejected (it is dead).
 */
function caseTest(dv: Val, l: CaseLabel, discNode: ts.Expression, env: Env): string {
  const t = dv.type;
  const e = l.node;
  const lit = ts.isNumericLiteral(e) ? e : ts.isPrefixUnaryExpression(e) && ts.isNumericLiteral(stripParens(e.operand)) ? (stripParens(e.operand) as ts.NumericLiteral) : null;
  if (t.k === "int" && lit) {
    const value = (lit === e ? 1 : -1) * Number(lit.text);
    if (!Number.isInteger(value)) fail(e, `case ${nodeText(e)} can never match: \`${nodeText(discNode, 30)}\` is an int, and ${nodeText(e)} is not an integer (remove the case)`);
    return `VReact.JS.eq ${paren(dv.code)} ${leanInt(BigInt(value))}`;
  }
  if (t.k === "num") {
    // IEEE equality, as === (NaN matches nothing, -0 matches 0): the opaque test
    const v = expr(e, env, T.num);
    return `(VReact.JS.Num.eq ${paren(dv.code)} ${paren(v.code)})`;
  }
  if (t.k !== "int" && t.k !== "str" && t.k !== "bool") fail(discNode, `switch on a value of type ${showType(t)} is not supported (only ints, strings, booleans, string-literal enums and discriminants x.kind)`);
  const v = expr(e, env, t);
  if (!sameType(v.type, t)) fail(e, `case label of type ${showType(v.type)} in a switch on ${showType(t)}`);
  return `VReact.JS.eq ${paren(dv.code)} ${paren(v.code)}`;
}

function switchStmt(s: ts.SwitchStatement, env: Env, bc: BlockCtx, rest: (e: Env) => string): string {
  const disc = stripParens(s.expression);
  const m = env.m;
  // collect clauses: groups of case labels sharing a body
  interface Group {
    labels: CaseLabel[];
    body: ts.Statement[];
    isDefault: boolean;
    node: ts.Node;
  }
  const groups: Group[] = [];
  let pending: CaseLabel[] = [];
  let pendingDefault = false;
  let pendingNode: ts.Node | null = null;
  for (const cl of s.caseBlock.clauses) {
    if (ts.isCaseClause(cl)) pending.push(caseLabel(cl.expression));
    else pendingDefault = true;
    pendingNode = pendingNode ?? cl;
    if (cl.statements.length === 0) continue;
    // a body ends with `break` (possibly as the last statement of a trailing block) or terminates
    const body = withoutTrailingBreak(cl.statements);
    if (!body && !terminates(cl.statements)) fail(cl, "switch cases must end with break, return or throw (no fall-through)");
    groups.push({ labels: pending, body: body ?? [...cl.statements], isDefault: pendingDefault, node: pendingNode });
    pending = [];
    pendingDefault = false;
    pendingNode = null;
  }
  // trailing labels without statements: they match and do nothing
  if (pendingNode) groups.push({ labels: pending, body: [], isDefault: pendingDefault, node: pendingNode });
  // JS takes the first case whose label matches, wherever `default` is; `default`
  // (in any position, possibly grouped with labels) takes every value no case matches.
  // (A literal label repeated later can never be taken there.)
  const claimed = new Set<string>();
  for (const g of groups) {
    g.labels = g.labels.filter((l) => l.key === null || !claimed.has(l.key));
    g.labels.forEach((l) => l.key !== null && claimed.add(l.key));
  }
  const defaultGroup = groups.find((g) => g.isDefault);
  const caseGroups = groups.filter((g) => !g.isDefault && g.labels.length > 0);
  const after = (e2: Env) => rest(e2);
  /** the string-literal labels of a switch on a discriminant / enum */
  const texts = (g: Group, what: string): string[] =>
    g.labels.map((l) => l.text ?? fail(l.node, `the case labels of a switch on ${what} must be string literals`));
  // discriminated union switch: switch (a.kind).  The base of `props.mode` / `e.key` is
  // not a value (only its fields are): no union then; the whole discriminant is typed below.
  if (ts.isPropertyAccessExpression(disc)) {
    let baseT: VType | null = null;
    try {
      baseT = typeOf(disc.expression, env);
    } catch (err) {
      if (!(err instanceof VtsError)) throw err;
    }
    if (baseT?.k === "union" && m.reg.union(baseT).tag === disc.name.text) {
      const u = m.reg.union(baseT);
      const target = expr(disc.expression, env);
      const key = pathKey(env, disc.expression);
      const h = m.fresh("h");
      const covered = new Set<string>();
      let arms = "";
      for (const g of groups) for (const l of texts(g, nodeText(disc, 30))) if (!u.variants.some((v) => v.lit === l)) fail(g.node, `"${l}" is not a variant of ${showType(baseT)}`);
      for (const g of caseGroups) {
        const ls = texts(g, nodeText(disc, 30));
        if (ls.length === 1) {
          const v = u.variants.find((v) => v.lit === ls[0])!;
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
          const pats = ls.map((l) => {
            const v = u.variants.find((v) => v.lit === l)!;
            covered.add(l);
            return `.${leanField(v.ctor)}${v.fields.map(() => " _").join("")}`;
          });
          arms += `\n  | ${pats.join(" | ")} => ${paren(block(g.body, 0, env, bc, after))}`;
        }
      }
      // values no case matches: the default body, or the code after the switch (last arm)
      if (covered.size < u.variants.length) arms += `\n  | _ => ${paren(defaultGroup ? block(defaultGroup.body, 0, env, bc, after) : rest(env))}`;
      return `(match ${h} : ${target.code} with${arms})`;
    }
  }
  // switch on an enum value: exhaustive match on its constructors
  const dv = expr(disc, env);
  if (dv.type.k === "enum") {
    const lits = m.reg.enumLits(dv.type);
    const covered = new Set<string>();
    let arms = "";
    for (const g of groups) for (const l of texts(g, nodeText(disc, 30))) if (!lits.includes(l)) fail(g.node, `"${l}" is not a member of ${showType(dv.type)}`);
    for (const g of caseGroups) {
      const ls = texts(g, nodeText(disc, 30));
      ls.forEach((l) => covered.add(l));
      arms += `\n  | ${ls.map((l) => `.${leanField(l)}`).join(" | ")} => ${paren(block(g.body, 0, env, bc, after))}`;
    }
    if (covered.size < lits.length) arms += `\n  | _ => ${paren(defaultGroup ? block(defaultGroup.body, 0, env, bc, after) : rest(env))}`;
    const h = m.fresh("h");
    return `(match ${h} : ${dv.code} with${arms})`;
  }
  // generic switch on a primitive value: if-chain (the labels of a group tested in order)
  let elseCode = defaultGroup ? block(defaultGroup.body, 0, env, bc, after) : rest(env);
  const tests = caseGroups.map((g) => {
    const ls = g.labels.map((l) => {
      const before = m.obCount();
      const code = caseTest(dv, l, disc, env);
      return { code, obs: m.obCount() > before };
    });
    if (!ls.slice(1).some((l) => l.obs)) return ls.map((l) => l.code).join(" || ");
    // a later label of the group is evaluated only when the earlier ones do not match (JS): its
    // obligations (`case 0: case xs[3]:`) are under their negation
    let acc = ls[ls.length - 1].code;
    for (let i = ls.length - 2; i >= 0; i--) acc = `(if ${m.fresh("h")} : (${ls[i].code}) = true then true else ${paren(acc)})`;
    return acc;
  });
  for (let gi = caseGroups.length - 1; gi >= 0; gi--) {
    const g = caseGroups[gi];
    const h = m.fresh("h");
    elseCode = `(if ${h} : (${tests[gi]}) = true then ${paren(block(g.body, 0, env, bc, after))} else ${paren(elseCode)})`;
  }
  return elseCode;
}

/**
 * The statements of a case body that ends with `break` (directly, or as the last
 * statement of a trailing block `{ …; break; }`), without that break; null otherwise.
 */
function withoutTrailingBreak(stmts: readonly ts.Statement[]): ts.Statement[] | null {
  const last = stmts[stmts.length - 1];
  if (!last) return null;
  if (ts.isBreakStatement(last) && !last.label) return stmts.slice(0, -1);
  if (ts.isBlock(last)) {
    const inner = withoutTrailingBreak(last.statements);
    if (inner) return [...stmts.slice(0, -1), ...inner];
  }
  return null;
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
  // locals assigned in the body; `sw`: the innermost enclosing breakable statement (inside
  // the loop body) is a switch, so an unlabeled `break` there only ends the case
  const assigned: ts.Symbol[] = [];
  const visit = (n: ts.Node, sw = false) => {
    if (ts.isBinaryExpression(n) && [ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.MinusEqualsToken].includes(n.operatorToken.kind) && ts.isIdentifier(n.left)) {
      const sym = symbolOf(env, n.left);
      if (sym && env.vars.has(sym) && !assigned.includes(sym)) assigned.push(sym);
    }
    if ((ts.isPostfixUnaryExpression(n) || ts.isPrefixUnaryExpression(n)) && ts.isIdentifier(n.operand) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) {
      const sym = symbolOf(env, n.operand);
      if (sym && env.vars.has(sym) && !assigned.includes(sym)) assigned.push(sym);
    }
    if (ts.isReturnStatement(n) || ts.isContinueStatement(n) || (ts.isBreakStatement(n) && (!!n.label || !sw))) fail(n, "return/break/continue inside for…of are not supported (a `break` may only end a switch case); use array methods (find, some, …)");
    if (ts.isCallExpression(n) && updateTarget(n.expression, env)) fail(n, "state updates inside loops are not supported; compute the new value, then update once");
    const inner = ts.isSwitchStatement(n) ? true : ts.isIterationStatement(n, false) ? false : sw;
    ts.forEachChild(n, (c) => visit(c, inner));
  };
  visit(s.statement);
  if (assigned.length === 0) fail(s, "loop has no effect (it assigns no local variable)");
  const accTypes = assigned.map((sym) => (env.vars.get(sym) as { type: VType }).type);
  const accCodes = assigned.map((sym) => (env.vars.get(sym) as { code: string }).code);
  // fresh names for accumulator and element (what was known about the assigned locals is forgotten)
  let e1 = env;
  for (const sym of assigned) e1 = forgetNarrowing(e1, sym);
  const accNames: string[] = [];
  for (const sym of assigned) {
    const r = freshLocal(e1, leanIdent(sym.name));
    e1 = r.env;
    accNames.push(r.name);
    e1 = dropNarrowing(bind(e1, sym, { k: "val", code: r.name, type: (env.vars.get(sym) as { type: VType }).type }), sym);
  }
  const decl = s.initializer.declarations[0];
  const pr = bindParam(decl.name, xs.type.elem, e1);
  const tuple = (names: string[]) => (names.length === 1 ? names[0] : `(${names.join(", ")})`);
  const bodyBc: BlockCtx = { kind: "value", fnNode: s, onReturn: () => fail(s, "return inside loop") };
  const body = block(blockOf(s.statement), 0, pr.env, bodyBc, (e3) => tuple(assigned.map((sym) => (e3.vars.get(sym) as { code: string }).code)));
  const accT = accTypes.length === 1 ? leanType(accTypes[0]) : `(${accTypes.map(leanType).join(" × ")})`;
  const fold = `(${paren(xs.code)}.foldl (fun (acc : ${accT}) (${pr.binder} : ${leanType(xs.type.elem)}) => let ${tuple(accNames)} := acc; ${body}) ${tuple(accCodes)})`;
  // rebind the assigned locals after the loop
  let e4 = env;
  for (const sym of assigned) e4 = forgetNarrowing(e4, sym);
  const outNames: string[] = [];
  for (const sym of assigned) {
    const r = freshLocal(e4, leanIdent(sym.name));
    e4 = dropNarrowing(bind(r.env, sym, { k: "val", code: r.name, type: (env.vars.get(sym) as { type: VType }).type }), sym);
    outNames.push(r.name);
  }
  return `(let ${tuple(outNames)} := ${fold};\n${rest(e4)})`;
}

/* ─────────────────────────── handlers ─────────────────────────── */

/**
 * Translate a function used as an event handler into `fun ev => outcome`.  `paramTs`: the
 * TypeScript types of the arguments (by default, those the context of `fnExpr` gives them, e.g.
 * the child's callback prop type for a JSX attribute), against which annotations are checked.
 */
export function handlerFn(fnExpr: ts.Expression, env: Env, kind: "discrete" | "robust", argTypes: Param[] | "event", hyps?: string, paramTs?: ts.Type[] | null): { code: string; params: string[] } {
  const m = env.m;
  const comp = env.comp!;
  fnExpr = stripParens(fnExpr);
  if (paramTs === undefined) paramTs = argTypes === "event" ? null : contextualParamTsTypes(fnExpr, env);
  // passing a closure by name
  if (ts.isIdentifier(fnExpr)) {
    const s = symbolOf(env, fnExpr);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "closure") return handlerFn(b.fn, { ...b.env, scope: env.scope }, kind, argTypes, hyps, paramTs);
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
      const r = bindParam(p.name, argTypes[i].type, e1, paramTs?.[i] ?? null);
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
  if (kind === "robust") fail(node, "parent callbacks cannot be invoked from effects, timers, continuous/default-priority events or onFocus/onBlur/onInvalid (robust handlers)");
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
  // every reference counts: identifiers anywhere in the body (template literals, spreads,
  // JSX, nested closures, element access, optional chains), shorthand properties `{ x }`
  // resolved to the variable `x`
  const visit = (n: ts.Node) => {
    if (ts.isIdentifier(n) && !(ts.isPropertyAccessExpression(n.parent) && n.parent.name === n)) {
      const shorthand = ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n;
      const s = shorthand ? env.m.checker.getShorthandAssignmentValueSymbol(n.parent) : symbolOf(env, n);
      const b = s ? env.vars.get(s) : undefined;
      if (b && (b.k === "val" || b.k === "closure" || b.k === "callback" || b.k === "jsx")) {
        // reactive value: covered if it, or a path starting with it, is listed
        let full: ts.Expression = n;
        while (!shorthand && ts.isPropertyAccessExpression(full.parent) && full.parent.expression === full) full = full.parent;
        const k1 = `#${symId(s!)}`;
        const kFull = shorthand ? k1 : pathKey(env, full);
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
