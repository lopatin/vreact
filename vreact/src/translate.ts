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
import { T, type VType, type TypeEnv, type Field, type Param, sameType, showType, leanType, sharedFields, type Variant, typeOfNode, kindsOfType, nullShape, checkValueType, propertyNameText, propertyName, isEqType, mentionsTVar, substType, type TField, type NamedType, collectionKind, collectionTypeArgs, isLibSymbol, mapType, setType, nonValuePart } from "./types.ts";
import { type Env, type Val, ModCtx, type Binding, type StateVar, type CompCtx, type HandlerAcc, type FnInfo, type CompInfo, type Global, type Narrowed, type DomSite, bind, extend, freshLocal, refSymbol } from "./ctx.ts";
import { VtsError, fail, leanField, leanAccessor, leanIdent, leanStr, jsStr, leanInt, paren, nodeText, argText, exprText, capitalize, relLoc, decodeJsxEntities } from "./util.ts";

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

/** The symbol a reference resolves to (a shorthand property `{ x }`, or its name, to the variable `x`). */
export function symbolOf(env: Env, node: ts.Node): ts.Symbol | undefined {
  return refSymbol(env.m.checker, node);
}

function resolved(env: Env, s: ts.Symbol | undefined): ts.Symbol | undefined {
  if (s && s.flags & ts.SymbolFlags.Alias) return env.m.checker.getAliasedSymbol(s);
  return s;
}

/**
 * Name of the `vreact/spec` function `callee` refers to, by its declaration (through import
 * aliases: `import { forall as all }` gives "forall"); a local or project function spelled like
 * one is not.
 */
export function specFn(env: Env, callee: ts.Expression): string | null {
  return env.m.prog.specName(callee);
}

const HOOKS = new Set(["useState", "useReducer", "useEffect", "useMemo", "useCallback", "useRef", "useContext", "useLayoutEffect", "useId", "useTransition", "useDeferredValue", "useSyncExternalStore", "useImperativeHandle"]);

/**
 * Name of the React hook `callee` (`useState`, `React.useState`, an import alias) refers to, by
 * its declaration in React's types; a local or project function spelled like a hook is not one.
 * The name (or the namespace before the dot) must be bound by an import of the program: React's
 * types also declare the UMD global `React`, which TypeScript lets a module use without an import
 * ("allowUmdGlobalAccess") but which a module bundle does not define (a ReferenceError).
 */
export function hookName(env: Env, callee: ts.Expression): string | null {
  const n = ts.isPropertyAccessExpression(callee) ? callee.name : callee;
  const name = env.m.prog.reactName(n);
  if (!name || !HOOKS.has(name)) return null;
  const root = ts.isPropertyAccessExpression(callee) ? callee.expression : callee;
  if (!ts.isIdentifier(root) || !env.m.prog.isImportBinding(root)) {
    fail(callee, `\`${nodeText(callee, 40)}\` is React's ${name} only through ${ts.isIdentifier(root) ? `\`${root.text}\`, which is not imported here (React's global \`React\` is declared by its types, but a module bundle does not define it: a ReferenceError)` : "an expression"}: import the hook (\`import { ${name} } from "react"\`, or \`import * as React from "react"\` and call \`React.${name}\`)`);
  }
  return name;
}

/** Globals the translation gives a meaning (for the message when a binding of the program is spelled like one). */
const BUILTIN_NAMES = new Set(["undefined", "Math", "String", "Array", "console", "localStorage", "document", "setTimeout", "setInterval", "clearTimeout", "clearInterval"]);

/** Does `n` refer to the JavaScript global `name` (`Math`, `console`, …; see `Program.isGlobal`)? */
export function isGlobal(env: Env, n: ts.Node, name: string): boolean {
  return env.m.prog.isGlobal(n, name);
}

function globalOf(env: Env, node: ts.Node): Global | undefined {
  const s = resolved(env, symbolOf(env, node));
  const d = s?.declarations?.[0];
  if (!d) return undefined;
  return env.m.prog.globals.get(d);
}

/** Array methods that mutate the array (rejected everywhere: VTS data is immutable). */
export const ARRAY_MUTATORS = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin"]);

/**
 * The values an external write evaluates, if `e` (an expression statement's expression) is one:
 * `console.*(…)` (its arguments), `localStorage.setItem(k, v)` (k and v), `document.title = v`
 * (v) — of the globals `console`, `localStorage` and `document` (see `isGlobal`).  Their values
 * are not modelled (nothing in the model reads the console, the storage or the title).
 */
function externalWriteArgs(e: ts.Expression, env: Env): readonly ts.Expression[] | null {
  e = stripParens(e);
  if (ts.isCallExpression(e) && externalWrite(e, env)) return e.arguments;
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken && isDocumentTitle(e.left, env)) return [e.right];
  return null;
}

/**
 * `JSON.stringify(v)` (also `(v, null)` and `(v, null, indent)` with a literal indent) of the
 * global `JSON`: the value `v`, else null.  It reads `v` (VTS values have no `toJSON`) and returns
 * a new string.
 */
function jsonStringifyValue(a: ts.Expression, env: Env): ts.Expression | null {
  a = stripParens(a);
  if (!ts.isCallExpression(a) || !ts.isPropertyAccessExpression(a.expression) || a.expression.name.text !== "stringify" || !isGlobal(env, stripParens(a.expression.expression), "JSON")) return null;
  const [v, replacer, indent] = a.arguments;
  if (!v || ts.isSpreadElement(v) || a.arguments.length > 3) return null;
  if (replacer && replacer.kind !== ts.SyntaxKind.NullKeyword) return null;
  if (indent && !ts.isNumericLiteral(indent) && !ts.isStringLiteral(indent)) return null;
  return v;
}

/**
 * Is `x` (an expression, its enclosing parentheses climbed) written out by an external write —
 * an argument of `console.*(…)` / `localStorage.setItem(…)`, the value of `document.title = …`,
 * or the value of a `JSON.stringify(…)` that is one — whose statement `exprStatement` takes as
 * that write?  JS converts or prints it then; nothing of it is kept that the model reads.
 */
function isExternalWriteValue(x: ts.Node, env: Env): boolean {
  const up = (n: ts.Node) => {
    while (ts.isParenthesizedExpression(n.parent)) n = n.parent;
    return n;
  };
  let a = up(x);
  const p = a.parent;
  if (ts.isCallExpression(p) && p.arguments[0] === a && jsonStringifyValue(p, env)) a = up(p);
  const w = a.parent;
  if (!(ts.isCallExpression(w) || ts.isBinaryExpression(w)) || !ts.isExpressionStatement(up(w).parent)) return false;
  return !!externalWriteArgs(w, env)?.includes(a as ts.Expression);
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
      const s = refSymbol(checker, n);
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
  checkCollectionMutation(body, env);
}

/* ───────────────────── Map / Set: mutation and aliasing ───────────────────── */

/** Map/Set methods that mutate (`set`/`add` return the receiver, `delete` a boolean, `clear` undefined). */
const MUTATORS = new Set(["set", "add", "delete", "clear"]);

/**
 * The declarations of the fresh local Maps / Sets whose mutation statements `checkCollectionMutation`
 * allowed: `mutateLocal` translates only those (as rebindings).
 */
const freshMutable = new WeakSet<ts.Node>();

/** Whether an expression is a Map or a Set by its TypeScript type (also for an unannotated `ensures` parameter: see `tsTypeOf`). */
function collKindOf(x: ts.Expression, env: Env): "map" | "set" | null {
  const t = tsTypeOf(x, env);
  return t ? collectionKind(env.m.checker.getNonNullableType(t), env.m.prog.typeEnv) : null;
}

/** `new Map(…)` / `new Set(…)` of the library (not a user class of that name): its kind, else null. */
function newKind(ne: ts.NewExpression, ck: ts.TypeChecker, tenv: TypeEnv): "map" | "set" | null {
  const callee = stripParens(ne.expression);
  if (!ts.isIdentifier(callee) || (callee.text !== "Map" && callee.text !== "Set")) return null;
  let sym = ck.getSymbolAtLocation(callee);
  if (sym && sym.flags & ts.SymbolFlags.Alias) sym = ck.getAliasedSymbol(sym);
  return isLibSymbol(sym, tenv) ? (callee.text === "Map" ? "map" : "set") : null;
}

/**
 * A freshly allocated Map / Set that no other code refers to: `new Map(…)`, `new Set(…)`, or a
 * `.set(…)` / `.add(…)` chain on one (`new Map(m).set(k, v)`).
 */
function isFreshCollection(e: ts.Expression, ck: ts.TypeChecker, tenv: TypeEnv): boolean {
  e = stripParens(e);
  if (ts.isNewExpression(e)) return newKind(e, ck, tenv) !== null;
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && ["set", "add"].includes(e.expression.name.text)) {
    return isFreshCollection(e.expression.expression, ck, tenv);
  }
  return false;
}

/** The text of a method receiver for a message, parenthesised unless it is a primary expression (`(s as Map<int, int>).set(…)`). */
function recvText(e: ts.Expression, max: number): string {
  const t = nodeText(e, max);
  const primary = ts.isIdentifier(e) || ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e) || ts.isCallExpression(e) || ts.isParenthesizedExpression(e) || ts.isNonNullExpression(e) || (ts.isNewExpression(e) && !!e.arguments) || e.kind === ts.SyntaxKind.ThisKeyword;
  return primary ? t : `(${t})`;
}

/** A mutating method (`set`/`add`/`delete`/`clear`) of the library's Map, Set, WeakMap or WeakSet. */
function isCollectionMutator(sym: ts.Symbol | undefined, tenv: TypeEnv): boolean {
  if (!sym || !isLibSymbol(sym, tenv)) return false;
  return (sym.declarations ?? []).some((d) => {
    const owner = d.parent;
    return (ts.isInterfaceDeclaration(owner) || ts.isClassDeclaration(owner)) && !!owner.name && ["Map", "Set", "WeakMap", "WeakSet"].includes(owner.name.text);
  });
}

/** `Array.from` of the library. */
function isArrayFrom(callee: ts.Expression, ck: ts.TypeChecker, tenv: TypeEnv): boolean {
  if (!ts.isPropertyAccessExpression(callee) || callee.name.text !== "from" || !ts.isIdentifier(callee.expression) || callee.expression.text !== "Array") return false;
  let sym = ck.getSymbolAtLocation(callee.expression);
  if (sym && sym.flags & ts.SymbolFlags.Alias) sym = ck.getAliasedSymbol(sym);
  return isLibSymbol(sym, tenv);
}

/** The receiver `n` of a mutation statement `n.set(…);` / `n.add(…);` / `n.delete(…);` / `n.clear();`. */
function mutationReceiver(n: ts.Node): ts.Identifier | null {
  if (!ts.isExpressionStatement(n)) return null;
  const e = stripParens(n.expression);
  if (!ts.isCallExpression(e) || !ts.isPropertyAccessExpression(e.expression) || !MUTATORS.has(e.expression.name.text)) return null;
  const r = stripParens(e.expression.expression);
  return ts.isIdentifier(r) ? r : null;
}

/** The variable a `for…of` iterates directly (`n`, `n.keys()`, `n.values()`, `n.entries()`), if any. */
function iteratedRoot(e: ts.Expression): ts.Identifier | null {
  e = stripParens(e);
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && ITER_METHODS.has(e.expression.name.text)) e = stripParens(e.expression.expression);
  return ts.isIdentifier(e) ? e : null;
}

/** The innermost function (arrow, function expression or declaration) containing `n`. */
function fnOf(n: ts.Node): ts.Node | undefined {
  for (let a = n.parent; a; a = a.parent) if (ts.isArrowFunction(a) || ts.isFunctionExpression(a) || ts.isFunctionDeclaration(a) || ts.isMethodDeclaration(a)) return a;
  return undefined;
}

/**
 * JS Maps and Sets are mutable objects shared by reference; the translation models them as
 * values, so a mutation is exact only on an object nothing else can observe.  Checked here for
 * one top-level function or component body, before it is translated:
 * * `set`/`add`/`delete`/`clear` are statements (`n.set(k, v);`), on a local `const n` of this
 *   body initialised with a fresh `new Map(…)` / `new Set(…)` (or a `.set`/`.add` chain on one) —
 *   never on parameters, props, state, constants, `let`s or values read from elsewhere; in an
 *   expression only `.set`/`.add` chains on a fresh copy (`new Map(m).set(k, v)`, a pure update);
 * * the mutations are in the function that declares `n` (not in a callback or helper, whose
 *   effect the translation would lose, and which may run later);
 * * no alias of `n` may exist when a mutation can still run: a use other than a read (`n.size`,
 *   `n.get(k)`, `n.has(k)`, an iteration consumed at once, a copy `new Map(n)`) — storing it in a
 *   record, array or variable, passing it to a function, setter or child, rendering it — must not
 *   be followed by a mutation (later in the code, or in a later iteration of an enclosing loop),
 *   except in the function's `return` (nothing of the function runs after it);
 * * a function that runs later (handler, effect, helper, functional update) may not refer to
 *   `n` when a mutation can follow its creation (JS closures see the object as it is when they run);
 * * no mutation inside a `for…of` that iterates `n` itself (JS visits added entries).
 * The allowed declarations are recorded in `freshMutable`, which `mutateLocal` requires.
 */
function checkCollectionMutation(body: ts.Node, env: Env) {
  const ck = env.m.checker;
  const tenv = env.m.prog.typeEnv;
  const kindOf = (x: ts.Expression) => collectionKind(ck.getNonNullableType(ck.getTypeAtLocation(x)), tenv);
  const muts = new Map<ts.Symbol, ts.CallExpression[]>();
  const collect = (n: ts.Node) => {
    // a Map/Set mutator reached other than as the callee of `x.m(…)` (the only form checked
    // below): `x["clear"]()`, `Map.prototype.set.call(x, …)`, `Reflect.apply(Set.prototype.add, x, …)`,
    // `x.set.bind(x)`, `(x.set)(k, v)`, `const f = x.delete` — wherever it is written, also in
    // arguments that are not otherwise translated (console.log(…)'s, an effect cleanup's)
    if (ts.isPropertyAccessExpression(n) && MUTATORS.has(n.name.text) && isCollectionMutator(ck.getSymbolAtLocation(n.name), tenv)) {
      if (!(ts.isCallExpression(n.parent) && n.parent.expression === n)) {
        fail(n, `${nodeText(n, 40)} is used without calling it directly (as in x.${n.name.text}(…)): VTS checks a Map/Set mutation only in that form; write const next = new Map(…) / new Set(…); next.${n.name.text}(…); on a fresh local copy`);
      }
    }
    if (ts.isElementAccessExpression(n) && kindOf(n.expression)) {
      fail(n, `${nodeText(n, 40)}: a Map or Set has no indexed elements (and x["set"] would reach its methods): use m.get(k), m.has(k), or index a spread copy ([...m.values()][i])`);
    }
    if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && MUTATORS.has(n.expression.name.text)) {
      const recv = stripParens(n.expression.expression);
      const kind = kindOf(recv);
      if (kind) {
        const name = n.expression.name.text;
        const Name = kind === "map" ? "Map" : "Set";
        const what = recvText(recv, 30);
        let st: ts.Node = n;
        while (ts.isParenthesizedExpression(st.parent)) st = st.parent;
        if (ts.isExpressionStatement(st.parent)) {
          if (ts.isCallExpression(recv) && ts.isPropertyAccessExpression(recv.expression) && MUTATORS.has(recv.expression.name.text)) {
            fail(n, `a chain of mutations as a statement: write one statement per mutation (n.${recv.expression.name.text}(…); n.${name}(…);)`);
          }
          const sym = ts.isIdentifier(recv) ? ck.getSymbolAtLocation(recv) : undefined;
          const d = sym?.valueDeclaration;
          const local = !!d && ts.isVariableDeclaration(d) && ts.isVariableDeclarationList(d.parent) && within(d, body);
          const isConst = local && ((d!.parent as ts.VariableDeclarationList).flags & ts.NodeFlags.Const) !== 0;
          const fresh = isConst && ts.isIdentifier((d as ts.VariableDeclaration).name) && !!(d as ts.VariableDeclaration).initializer && isFreshCollection((d as ts.VariableDeclaration).initializer!, ck, tenv);
          if (!sym || !fresh) {
            const why = !local
              ? "is not a local variable of this function (a parameter, prop, state value, constant, or a value read from one: the caller, React or other code holds the same object, and would see the change)"
              : !isConst
                ? "is declared with `let` (it may hold a shared object): declare the copy with `const`"
                : "is not initialised with a fresh new Map(…) / new Set(…) (it may be shared with whatever it was read from)";
            fail(n, `${what}.${name}(…) mutates ${what}, which ${why}; mutate a fresh copy instead: const next = new ${Name}(${what}); next.${name}(…);${name === "set" || name === "add" ? ` (or, in an expression, new ${Name}(${what}).${name}(…))` : ""}`);
          }
          muts.set(sym, [...(muts.get(sym) ?? []), n]);
        } else if (!((name === "set" || name === "add") && isFreshCollection(recv, ck, tenv))) {
          const returns = name === "delete" ? "returns a boolean" : name === "clear" ? "returns undefined" : `returns the same ${Name}`;
          fail(n, `${what}.${name}(…) in an expression: it mutates ${what} and ${returns}; VTS allows it only as a statement on a fresh local copy (const n = new ${Name}(…); n.${name}(…);)${name === "set" || name === "add" ? `, or in a chain on a fresh copy (new ${Name}(${what}).${name}(…))` : ""}`);
        }
      }
    }
    ts.forEachChild(n, collect);
  };
  collect(body);
  for (const [sym, ws] of muts) {
    const d = sym.valueDeclaration as ts.VariableDeclaration;
    const F = fnOf(d);
    const nm = sym.name;
    const Name = kindOf(d.name as ts.Identifier) === "set" ? "Set" : "Map";
    for (const w of ws) {
      if (fnOf(w) !== F) {
        fail(w, `\`${nm}\` is declared outside this function: mutating it from inside a function or callback is not supported (the translation would lose the mutation, and the function may run later); build the ${Name} where it is used, or with for…of instead of a callback`);
      }
    }
    /**
     * `x` is in a `return` statement of F itself (crossing no function): nothing of F runs after
     * it.  A `return` of a nested function (an array callback's `{ return n; }`, a `useMemo`
     * callback) only hands `n` back to F, which goes on running (and mutating).
     */
    const inReturn = (x: ts.Node): boolean => {
      for (let a = x.parent; a && a !== F; a = a.parent) {
        if (ts.isFunctionLike(a)) return false;
        if (ts.isReturnStatement(a)) return fnOf(a) === F;
      }
      return false;
    };
    /** May a mutation of `n` run after `at` (a use, or the creation of a function)? */
    const later = (at: ts.Node): boolean => {
      if (inReturn(at)) return false;
      if (ws.some((w) => w.getStart() >= at.end || within(at, w))) return true;
      // a loop around `at` (inside the variable's scope) runs the mutations in it again
      for (let a = at.parent; a && a !== F; a = a.parent) {
        if (ts.isForOfStatement(a) && !within(d, a) && ws.some((w) => within(w, a))) return true;
      }
      return false;
    };
    const checkRef = (r: ts.Identifier) => {
      let top: ts.Node = r;
      while (ts.isParenthesizedExpression(top.parent)) top = top.parent;
      const p = top.parent;
      // the receiver of a mutation statement
      if (ts.isPropertyAccessExpression(p) && p.expression === top && ws.some((w) => w.expression === p)) return;
      // referred to by a function that runs later
      for (let g = fnOf(r); g && g !== F; g = fnOf(g)) {
        if ((ts.isArrowFunction(g) || ts.isFunctionExpression(g)) && !isImmediateFn(g, env) && later(g)) {
          fail(r, `this function refers to \`${nm}\`, which is mutated after the function is created: a JS closure sees the ${Name} as it is when the closure runs, not as it is here; copy it first (\`const ${nm}Now = new ${Name}(${nm});\`) and use the copy, or create the function after the last mutation`);
        }
      }
      // reads: n.size, n.get(k), n.has(k), iteration consumed at once, copies
      if (ts.isPropertyAccessExpression(p) && p.expression === top) {
        const m = p.name.text;
        if (m === "size") return;
        if (["get", "has", "keys", "values", "entries"].includes(m) && ts.isCallExpression(p.parent) && p.parent.expression === p) return;
      }
      if (ts.isSpreadElement(p) && ts.isArrayLiteralExpression(p.parent)) return;
      if (ts.isForOfStatement(p) && p.expression === top) return;
      if (ts.isNewExpression(p) && p.arguments?.[0] === top && newKind(p, ck, tenv)) return;
      if (ts.isCallExpression(p) && p.arguments[0] === top && isArrayFrom(p.expression, ck, tenv)) return;
      // logged or written out where it stands (console.log("start", n), localStorage.setItem(k,
      // JSON.stringify(n)), document.title = …): the external write prints or converts the
      // Map/Set when it runs, and the model reads nothing of what it keeps
      if (isExternalWriteValue(top, env)) return;
      // anything else makes an alias (stored, passed, rendered, returned from a callback, …)
      if (later(r)) {
        fail(r, `\`${nm}\` is used here (stored, passed or rendered) and mutated afterwards: in JS both refer to the same ${Name}, so the later mutation also changes what is used here (the translation would keep the earlier contents); do the mutations first, or use a copy here (new ${Name}(${nm}))`);
      }
    };
    const visitRefs = (x: ts.Node) => {
      if (ts.isIdentifier(x) && x !== d.name && refSymbol(ck, x) === sym) checkRef(x);
      if (ts.isForOfStatement(x)) {
        const root = iteratedRoot(x.expression);
        if (root && refSymbol(ck, root) === sym) {
          const w = ws.find((w) => within(w, x.statement));
          if (w) fail(w, ITERATE_MUTATE_MSG(nm));
        }
      }
      ts.forEachChild(x, visitRefs);
    };
    visitRefs(F ?? body);
    freshMutable.add(d);
  }
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

/** `null`, or the global `undefined` (not a binding spelled `undefined`). */
export function isNullLit(e: ts.Expression, env: Env): boolean {
  return e.kind === ts.SyntaxKind.NullKeyword || isGlobal(env, e, "undefined");
}

export function stripParens(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) && e.type.getText() === "const") e = ts.isParenthesizedExpression(e) ? e.expression : (e as ts.AsExpression).expression;
  return e;
}

/** A conditional expression with a `null`/`undefined` leaf (`c ? x : null`, `c ? x : d ? y : null`). */
function hasNullLeaf(e: ts.Expression, env: Env): boolean {
  e = stripParens(e);
  if (isNullLit(e, env)) return true;
  return ts.isConditionalExpression(e) && (hasNullLeaf(e.whenTrue, env) || hasNullLeaf(e.whenFalse, env));
}

/** The type of some non-null leaf of a conditional (typed in its narrowed environment, nothing emitted). */
function nonNullLeafType(e: ts.Expression, env: Env): VType | undefined {
  e = stripParens(e);
  if (isNullLit(e, env)) return undefined;
  if (ts.isConditionalExpression(e) && hasNullLeaf(e, env)) {
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
  // `x!` (not inside an optional chain, `a?.b!.c`, which is still undefined when `a` is nullish)
  if (ts.isNonNullExpression(e)) {
    const base = ts.isOptionalChain(e) ? null : tsTypeOf(e.expression, env);
    return base ? ck.getNonNullableType(base) : null;
  }
  /**
   * A link of an optional chain (`r.get(k)?.name`, `r.get(k)?.a.b`, `r.get(k)?.[0]`) is
   * `undefined` when the chain stops at a `?.` whose base is nullish: TypeScript checks every
   * link on the non-nullish base, so a nullish base here comes from such a stop.
   */
  const chained = (base: ts.Type, t: ts.Type) => (ts.isOptionalChain(e) && ck.getNonNullableType(base) !== base ? ck.getNullableType(t, ts.TypeFlags.Undefined) : t);
  if (ts.isPropertyAccessExpression(e)) {
    const base = tsTypeOf(e.expression, env);
    if (!base) return null;
    const p = ck.getPropertyOfType(ck.getNonNullableType(base), e.name.text);
    return p ? chained(base, ck.getTypeOfSymbolAtLocation(p, e)) : null;
  }
  if (ts.isElementAccessExpression(e)) {
    const base0 = tsTypeOf(e.expression, env);
    if (!base0) return null;
    const base = ck.getNonNullableType(base0);
    if (ck.isTupleType(base)) {
      const i = stripParens(e.argumentExpression);
      const args = ck.getTypeArguments(base as ts.TypeReference);
      return ts.isNumericLiteral(i) && /^\d+$/.test(i.text) && Number(i.text) < args.length ? chained(base0, args[Number(i.text)]) : null;
    }
    const t = ck.getIndexTypeOfType(base, ts.IndexKind.Number);
    return t ? chained(base0, t) : null;
  }
  // `r.get(k)`, `r.at(i)` on a Map / Set / array whose TypeScript type is known (an unannotated
  // `ensures` parameter): the result type of the method's only, non-generic signature
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression)) {
    const base0 = tsTypeOf(e.expression.expression, env);
    if (!base0) return null;
    const base = ck.getNonNullableType(base0);
    if (!collectionKind(base, env.m.prog.typeEnv) && !ck.isArrayType(base) && !ck.isTupleType(base)) return null;
    const p = ck.getPropertyOfType(base, e.expression.name.text);
    const sigs = p ? ck.getSignaturesOfType(ck.getTypeOfSymbolAtLocation(p, e.expression), ts.SignatureKind.Call) : [];
    return sigs.length === 1 && !sigs[0].typeParameters?.length ? chained(base0, sigs[0].getReturnType()) : null;
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
  const fix = `${untypedFix(e, env, "give the parameter it comes from its exact type")}, so that TypeScript checks it`;
  fail(e, `\`${what}\` has TypeScript type any, so TypeScript does not check it against the type \`${ck.typeToString(slot)}\` expected here (that type says whether a missing value is null or undefined), and it is ${has}: ${fix}`);
}

/**
 * How to give `e` a TypeScript type: when it is computed from the unannotated parameter of an
 * `ensures((r) => …)`, by annotating that parameter with the function's return type.
 */
function untypedFix(e: ts.Expression, env: Env, otherwise: string): string {
  // the variable it is computed from (`r` in `r.v[0]`, `r.find(…)`, `r.get(k)?.name`)
  let root: ts.Expression = stripParens(e);
  while (ts.isPropertyAccessExpression(root) || ts.isElementAccessExpression(root) || ts.isCallExpression(root) || ts.isNonNullExpression(root)) root = stripParens(root.expression);
  if (!ts.isIdentifier(root)) return otherwise;
  const rs = ts.isShorthandPropertyAssignment(root.parent) && root.parent.name === root ? symbolOf(env, root.parent) : symbolOf(env, root);
  const rt = ensuresResultType(rs, env);
  return rt ? `annotate the result parameter with the return type, ensures((${root.text}: ${nodeText(rt, 50)}) => …)` : otherwise;
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
  if (!k) fail(node, `cannot tell whether \`${what}\` may be null or undefined (its TypeScript type is any or unknown): ${untypedFix(other, env, "give it its exact type (e.g. ensures((r: T | null) => …))")} or compare with == null`);
  if (k.null && k.undef) fail(node, `\`${what}\` may be null or undefined, which VTS does not distinguish: compare with == null / != null`);
  // the test as written (`!==` is always true where `===` is always false)
  const neg = op === ts.SyntaxKind.ExclamationEqualsEqualsToken;
  const [eq, loose, always] = neg ? ["!==", "!=", "true"] : ["===", "==", "false"];
  if (litText === "null" && k.undef && !k.null) {
    fail(node, `\`${what}\` can be undefined but never null (optional fields, find(), at(), a Map's get() and ?. give undefined), so \`${eq} null\` is always ${always} in JS: write ${eq} undefined or ${loose} null`);
  }
  if (litText === "undefined" && k.null && !k.undef) {
    fail(node, `\`${what}\` can be null but never undefined, so \`${eq} undefined\` is always ${always} in JS: write ${eq} null or ${loose} null`);
  }
}

/** `a === b` on two possibly-nullish values: both must use the same nullish value (null !== undefined). */
function checkOptionalEquality(node: ts.Node, a: ts.Expression, b: ts.Expression, env: Env) {
  const ka = nullishKinds(a, env);
  const kb = nullishKinds(b, env);
  if (!ka || !kb) fail(node, `cannot tell whether the operands may be null or undefined (TypeScript type any or unknown): ${untypedFix(!ka ? a : b, env, "give them their exact types")}`);
  const any = (k: { null: boolean; undef: boolean }) => k.null || k.undef;
  if (!any(ka) || !any(kb)) return;
  if ((ka.null && ka.undef) || (kb.null && kb.undef) || ka.null !== kb.null) {
    fail(node, `\`${nodeText(node, 50)}\` compares values that may be null and undefined (null !== undefined in JS, but VTS represents both as absent): narrow with != null first`);
  }
}

/**
 * Values JS compares by value (`===`, SameValueZero in includes/indexOf/Set): booleans, ints,
 * strings, enums, type parameters with an equality constraint (`isEqType`), options of these.
 */
function isPrimitiveEq(t: VType): boolean {
  if (t.k === "opt") return isPrimitiveEq(t.elem);
  return isEqType(t);
}

/** Why values of a type parameter without an equality constraint cannot be compared. */
function noEqMsg(t: VType & { k: "tvar" }, what: string): string {
  return `${what} on values of the type parameter ${t.name} is not supported: ${t.name} has no equality constraint, and JS compares objects and arrays by identity (and numbers by IEEE rules); declare ${t.name} extends int | string | boolean (or a string-literal enum type) to compare its values`;
}

/**
 * Why an operation on a value of a type parameter is rejected: its values are abstract in the
 * generic function's body (proved once for every instantiation), even under `T extends int`.
 */
function abstractMsg(t: VType & { k: "tvar" }, what: string): string {
  return `${what} a value of the type parameter ${t.name} is not supported: its values are abstract in the generic function (the body is checked once, for every type ${t.name} may be${t.eq ? ", even with an equality constraint" : ""}); only passing, storing, returning${t.eq ? ", ===" : ""}${t.fields ? " and its constrained fields" : ""} are available. Compute such values outside, or pass them as parameters of a concrete type`;
}

function tvarPart(t: VType): (VType & { k: "tvar" }) | null {
  const u = t.k === "opt" ? t.elem : t;
  return u.k === "tvar" ? u : null;
}

/**
 * An operand JS tests for truthiness (`if`, `?:`, `!`, `&&`, `||`, a contract): a boolean.  A
 * value of a type parameter (TypeScript accepts any type there) is rejected with the reason,
 * not as a type mismatch: whether it is truthy depends on what the type parameter is.
 */
function boolOperand(e: ts.Expression, env: Env): Val {
  try {
    return expr(e, env, T.bool);
  } catch (err) {
    if (!(err instanceof VtsError)) throw err;
    // (TypeScript may type a reference by the constraint, `boolean` for `K extends boolean`: the
    // operand's own VTS type tells)
    let t: VType | null = null;
    try {
      t = typeOf(e, env);
    } catch {
      // (the original error stands)
    }
    const tv = t && tvarPart(t);
    if (tv) {
      fail(e, t!.k === "opt"
        ? `truthiness of ${showType(t!)} is not supported: a present value of the type parameter ${tv.name} may be falsy too (0, "", false); compare with null explicitly (x !== null)`
        : `truthiness of a value of the type parameter ${tv.name} is not supported: whether it is truthy depends on the type ${tv.name} is instantiated with (0, "" and false are falsy, objects are truthy), and its values are abstract in the generic function; compare explicitly${tv.eq ? ` (x === y with another ${tv.name})` : ""}, or pass a boolean`);
    }
    if (t?.k === "opt" && err.message.startsWith("type mismatch: expected boolean")) {
      // (shown with the nullish value TypeScript gives it: `m.get(k)` is undefined, never null)
      const k = nullishKinds(e, env);
      const test = !k || (k.null && k.undef) ? "!= null" : k.undef ? "!== undefined" : "!== null";
      const what = nodeText(e, 30);
      fail(e, `\`${what}\` is ${showWithKinds(t, tsTypeOf(e, env), env)}, and a boolean is needed here: JS would test its truthiness (null and undefined are falsy, and so are 0, "", false and NaN); compare explicitly (${what} ${test}), or give a default with ?? (${what} ?? …)`);
    }
    throw err;
  }
}

/**
 * An index (or array) parameter of an array-method callback other than `map`'s: JS passes
 * `(element, index, array)`, VTS models the element only (`n` parameters: 2 for `reduce`'s
 * accumulator and element).  Rejected with what to write instead.
 */
function noIndexParam(name: string, fn: ts.Expression | undefined, n = 1) {
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) || fn.parameters.length <= n) return;
  const p = fn.parameters[n];
  const what = n === 2 ? "the accumulator and the element" : "the element";
  fail(p, `${name} callbacks take only ${what} in VTS (an index parameter is supported for map only, \`xs.map((x, i) => …)\`): for a condition on positions write forall(0, xs.length, (i) => … xs[i] …)${name === "every" ? " (e.g. a.length === b.length && forall(0, a.length, (i) => a[i] === b[i]))" : ""}`);
}

/** Element comparisons of `includes`/`indexOf`/`distinct` are by value only for primitive elements. */
function checkPrimitiveElems(node: ts.Node, arr: ts.Expression, elem: VType, what: string, env: Env) {
  if (elem.k === "num") fail(node, `${what} on number elements is not supported (JS compares the elements with SameValueZero or ===, where NaN and -0 are special; numbers are opaque in VTS); use ints`);
  const tv = tvarPart(elem);
  if (tv && !tv.eq) fail(node, noEqMsg(tv, what));
  if (!isPrimitiveEq(elem)) {
    fail(node, `${what} on ${showType(elem)} elements compares object identity in JS (a copy is never found): compare keys instead, e.g. xs.some((x) => x.id === v.id)`);
  }
  if (elem.k === "opt") {
    const et = elemTsType(arr, env);
    const k = et ? kindsOfType(et) : null;
    if (!k || (k.null && k.undef)) fail(node, `${what} on elements that may be null or undefined is not supported (VTS does not distinguish them)`);
  }
}

/**
 * `xs.includes(null)` / `xs.indexOf(undefined)` on optional elements: JS compares each element
 * with the nullish value only, and a present value (a type parameter's, a record's, a number's)
 * never equals it, so the search is a nullishness test for every element type (no equality
 * constraint needed).  The literal must be the nullish value the elements can hold (JS `undefined`
 * is not `null`).  Whether `arg` is such a literal (then the caller tests `Option.isNone`).
 */
function nullishSearch(node: ts.Node, arr: ts.Expression, elem: VType, arg: ts.Expression | undefined, what: string, env: Env): boolean {
  if (!arg || elem.k !== "opt" || !isNullLit(stripParens(arg), env)) return false;
  const et = elemTsType(arr, env);
  const k = et ? kindsOfType(et) : null;
  if (!k || (k.null && k.undef)) fail(node, `${what} on elements that may be null or undefined is not supported (VTS does not distinguish them)`);
  const lit = stripParens(arg).kind === ts.SyntaxKind.NullKeyword ? "null" : "undefined";
  const never = lit === "null" ? !k.null : !k.undef;
  if (never) {
    const other = lit === "null" ? "undefined" : "null";
    fail(node, `the elements can be ${other} but never ${lit}, so ${what}(${lit}) ${what === "includes" ? "is always false" : "is always -1"} in JS (${other} !== ${lit}): search for ${other}`);
  }
  return true;
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
  if (t.k === "map") return hasOptPart(t.key) || hasOptPart(t.val);
  if (t.k === "set") return hasOptPart(t.elem);
  // records, unions, enums: nominal (their fields' kinds are those of the declaration); a type
  // parameter: never nullish, and its instantiation's parts are not looked at where it is in scope
  return false;
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
  if ((vt.k === "map" || vt.k === "set") && t) {
    const args = collectionTypeArgs(t, ck);
    const parts = vt.k === "map" ? [vt.key, vt.val] : [vt.elem];
    if (args && args.length === parts.length) return `${vt.k === "map" ? "ReadonlyMap" : "ReadonlySet"}<${parts.map((p, i) => showWithKinds(p, args[i], env)).join(", ")}>`;
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
  checkNotThisParam(p);
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
 * TypeScript's `this` parameter (`function (this: T, x) {…}`) is not a parameter: it types the
 * receiver, and the arguments go to the parameters after it.  VTS binds parameters to arguments
 * by position, so it would give `x` the second argument where JS gives it the first.
 */
export function checkNotThisParam(p: ts.ParameterDeclaration) {
  if (ts.isIdentifier(p.name) && p.name.text === "this") {
    fail(p, "a `this` parameter is not supported: it is not a parameter (it types the receiver, and JS passes the arguments to the parameters after it); remove it");
  }
}

/**
 * The parameters of a function VTS binds to the arguments by position (a local helper inlined
 * at its calls, a callback, an event handler, a component): a `this` parameter (not a
 * parameter), a rest parameter (an array of the remaining arguments), a default value (used
 * when the argument is undefined) and an optional parameter (`x?: T` receives `T | undefined`)
 * would each give a parameter another value than the argument at its position.
 */
export function checkPlainParams(ps: readonly ts.ParameterDeclaration[], what: string) {
  for (const p of ps) {
    checkNotThisParam(p);
    const pname = p.name.getText();
    if (p.dotDotDotToken) fail(p, `a rest parameter \`...${pname}\` of ${what} is not supported (JS collects the remaining arguments into an array): take an array parameter instead`);
    if (p.initializer) fail(p.initializer, `a default value for parameter \`${pname}\` of ${what} is not supported (JS uses it when the argument is undefined): pass the value at every call`);
    if (p.questionToken) fail(p, `optional parameter \`${pname}?\` of ${what} is not supported: declare it \`${pname}: T | undefined\` and pass it at every call`);
  }
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
  // (keys exactly: number is no key type)
  if (ann.k === "map" && real.k === "map") return sameType(ann.key, real.key) && annotationFits(ann.val, real.val);
  return sameType(ann, real);
}

/** `distinct(xs, key)` compares keys with SameValueZero (a JS Set): keys must be ints or strings (or enums, or an equality-constrained type parameter). */
function checkDistinctKey(node: ts.Node, t: VType) {
  if (t.k === "tvar" && !t.eq) fail(node, noEqMsg(t, "distinct (keys compared with SameValueZero)"));
  if (!isEqType(t) || t.k === "bool") fail(node, `distinct keys must be int or string (got ${showType(t)})`);
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
export function isNumeric(t: VType) {
  return t.k === "int" || t.k === "num";
}

/** Insert a coercion from `v.type` to `expected` where VTS allows one. */
export function coerce(v: Val, expected: VType | undefined, node: ts.Node, env: Env): Val {
  if (!expected || sameType(v.type, expected)) return v;
  const w = widen(v, expected, env);
  if (w) return w;
  if (expected.k === "void" || expected.k === "unit") return v;
  const tv = tvarPart(v.type) ?? tvarPart(expected);
  // (TypeScript's ReadonlyMap / ReadonlySet are covariant: `ReadonlyMap<int, int>` where
  // `ReadonlyMap<int, number>` or `ReadonlySet<E>` where `ReadonlySet<string>` is expected)
  const coll = (v.type.k === "map" && expected.k === "map") || (v.type.k === "set" && expected.k === "set")
    ? ` (VTS has no Map/Set covariance: the key, value and element types must be exactly the same; e.g. give a generic helper's arguments the same ${v.type.k === "map" ? "Map" : "Set"} types)`
    : "";
  fail(node, `type mismatch: expected ${showType(expected)}, got ${showType(v.type)}${tv ? ` (a value of the type parameter ${tv.name} is abstract: it is a ${tv.name} and nothing else)` : coll}`);
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
  // the base of an optional chain's `?.`, bound to its present value (see `optionalChain`)
  const bound = chainBound.get(e);
  if (bound) return bound;
  // narrowed path? (a variant narrowing replaces a `some` one: `s: T | null` tested non-null,
  // then to be a variant, is that present value)
  const key = pathKey(env, e);
  if (key) {
    const n = env.narrow.get(key);
    if (n && (n.kind === "some" || n.kind === "variant")) return { code: n.code, type: n.type };
  }
  const chain = optionalChain(e, env);
  if (chain) return chain;
  switch (e.kind) {
    case ts.SyntaxKind.ParenthesizedExpression:
      return expr((e as ts.ParenthesizedExpression).expression, env, expected);
    case ts.SyntaxKind.NumericLiteral: {
      // literals are always type-ascribed: a bare Lean numeral defaults to Nat (truncated subtraction)
      const text = (e as ts.NumericLiteral).text;
      // (TypeScript normalises a literal beyond the doubles, `1e400`, to "Infinity": that number
      // is what JS reads it as, the Lean literal 1e400 stands for it)
      if (!Number.isFinite(Number(text))) return { code: "(1e400 : VReact.JS.Num)", type: T.num };
      if (expected?.k === "num" || /[.eE]/.test(text)) {
        // an integer literal as a number is `Num.ofInt n`, the form of an int used as a number
        // (`x === 0` with `x : number` and a divisor's `x !== 0` obligation are then one term)
        if (/^\d+$/.test(text)) return { code: `(VReact.JS.Num.ofInt ${leanInt(BigInt(text))})`, type: T.num };
        return { code: `(${text} : VReact.JS.Num)`, type: T.num };
      }
      return { code: leanInt(BigInt(text)), type: T.int };
    }
    case ts.SyntaxKind.StringLiteral:
    case ts.SyntaxKind.NoSubstitutionTemplateLiteral: {
      const text = jsxAttrText(e as ts.StringLiteral);
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
      if (!ty && hasNullLeaf(c, env)) {
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
    case ts.SyntaxKind.NewExpression:
      return newCollection(e as ts.NewExpression, env, expected);
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

/**
 * The JS value of a string literal: the text TypeScript gives, except for a JSX attribute
 * string (`title="a &amp; b"`), whose character references JS decodes.
 */
export function jsxAttrText(e: ts.StringLiteralLike): string {
  if (!e.parent || !ts.isJsxAttribute(e.parent)) return e.text;
  // Babel's JSX transform replaces a line break and the whitespace after it by one space
  // (`/\n\s+/g`, on the value with its character references decoded), TypeScript's keeps the
  // text: the value would depend on the compiler.  So a line break is rejected, whether
  // written as one or as a reference (`&#10;`, `&#xA;`, `&#13;`)
  const hasBreak = (s: string) => [...s].some((c) => ts.isLineBreak(c.charCodeAt(0)));
  const why = "JSX compilers do not agree on its value (Babel replaces a line break and the whitespace after it with one space, TypeScript keeps them)";
  if (hasBreak(e.text)) fail(e, `a line break inside a JSX attribute string: ${why}; write the string on one line, or as an expression {"…"}`);
  const value = decodeJsxEntities(e.text, e);
  if (hasBreak(value)) fail(e, `a character reference to a line break inside a JSX attribute string: ${why}; write the string as an expression with an escape, e.g. {${JSON.stringify(value)}}`);
  return value;
}

/**
 * The bases of the `?.` links being translated (`optionalChain`), bound to their present
 * values: the rest of the chain is translated with the base replaced by its value.
 */
const chainBound = new Map<ts.Node, Val>();

/**
 * An optional chain (`x?.f`, `a?.f.g`, `m.get(k)?.has(x)`, `g.get(r)?.get(c)`, `xs?.[i]`,
 * `a?.b.c?.d(x)`): when the base before the first `?.` is null/undefined, JS skips the whole
 * rest of the chain and gives `undefined`.  Translated as a match on the base,
 * `(match h : base with | some v => some rest(v) | none => none)` (the rest's own `?.` links
 * nest the same way; `h` is there for the rest's obligations).  Returns null for an expression
 * that is not the end of such a chain; `a?.b!` is translated by the non-null assertion
 * (TypeScript's `!` asserts the whole chain, `propertyAccess` translates its `a?.b`).
 */
function optionalChain(e: ts.Expression, env: Env): Val | null {
  if (!ts.isOptionalChain(e) || ts.isNonNullExpression(e)) return null;
  // (a link inside a longer chain is translated as part of that chain)
  const p = e.parent;
  if (ts.isOptionalChain(p) && (p as ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression).expression === e) return null;
  // the first `?.` whose base is not bound yet
  let link: ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | null = null;
  for (let n: ts.Expression = e; ts.isOptionalChain(n); ) {
    const x = n as ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression;
    if (chainBound.has(x.expression)) break;
    if (!ts.isNonNullExpression(x) && x.questionDotToken) link = x;
    n = x.expression;
  }
  if (!link) return null;
  if (ts.isCallExpression(link)) fail(link, `an optional call \`${nodeText(link.expression, 30)}?.(…)\` is not supported (functions are never optional in VTS): call it directly`);
  const baseE = link.expression;
  const base = expr(baseE, env);
  if (base.type.k !== "opt" && !isPresentValue(base.type)) fail(link, "?. on a non-optional value");
  const present = base.type.k === "opt" ? base.type.elem : base.type;
  const { env: e1, name: v } = base.type.k === "opt" ? freshLocal(env, "v") : { env, name: base.code };
  chainBound.set(baseE, { code: base.type.k === "opt" ? v : base.code, type: present });
  let rest: Val;
  try {
    rest = expr(e, e1);
  } finally {
    chainBound.delete(baseE);
  }
  if (base.type.k !== "opt") return rest; // `?.` on a present (e.g. narrowed) value: nothing to skip
  const t = rest.type.k === "opt" ? rest.type : T.opt(rest.type);
  const h = env.m.fresh("h");
  const some = rest.type.k === "opt" ? rest.code : `some ${paren(rest.code)}`;
  return { code: `(match ${h} : ${base.code} with\n  | some ${v} => ${paren(some)}\n  | none => (none : ${leanType(t)}))`, type: t };
}

/**
 * The advice for a property or method used on a possibly-null value `x` (the receiver
 * expression): the nullish value TypeScript gives it (`m.get(k)` is `undefined`, never `null`).
 */
function narrowAdvice(x: ts.Expression | undefined, env: Env): string {
  const k = x ? nullishKinds(x, env) : null;
  const test = !k ? "!= null" : k.null && k.undef ? "!= null" : k.undef ? "!== undefined" : "!== null";
  const what = x ? nodeText(x, 30) : "x";
  const simple = !!x && (ts.isIdentifier(stripParens(x)) || ts.isPropertyAccessExpression(stripParens(x)));
  return simple
    ? `narrow it with ${what} ${test} first, or use ?. (${what}?.… ?? default)`
    : `use ?. (${what}?.… ?? default), or name it and narrow: const v = ${what}; if (v ${test}) …`;
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
    case "tvar":
      fail(node, abstractMsg(v.type, "converting to a string"));
    default:
      fail(node, `cannot convert ${showType(v.type)} to a string`);
  }
}

function identifier(id: ts.Identifier, env: Env, expected?: VType, symOverride?: ts.Symbol): Val {
  if (isGlobal(env, id, "undefined")) {
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
    if (b.k === "timer") fail(id, `\`${id.text}\` is a timer handle: it can only be cleared, with clearTimeout(${id.text}) / clearInterval(${id.text}) in the effect's cleanup`);
  }
  const g = s && symOverride ? (() => { const d = resolved(env, s)?.declarations?.[0]; return d ? env.m.prog.globals.get(d) : undefined; })() : globalOf(env, id);
  if (g?.k === "const") {
    env.m.deps.add(g.info.qname);
    return { code: g.info.qname, type: g.info.type };
  }
  if (g?.k === "fn") fail(id, "functions are not first-class in VTS; call the function instead");
  if (BUILTIN_NAMES.has(id.text) && !isGlobal(env, id, id.text)) {
    fail(id, `\`${id.text}\` here is not JavaScript's global ${id.text}: it is ${s?.declarations?.length ? `declared at ${relLoc(s.declarations[0], env.m.prog.root)}` : "a binding of this program"} (a name is recognised by its declaration, not its spelling); rename it`);
  }
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
  const root = (x: ts.Expression): Extract<Binding, { k: "event" }> | undefined => {
    if (!ts.isIdentifier(x)) return undefined;
    const s = symbolOf(env, x);
    const b = s ? env.vars.get(s) : undefined;
    return b?.k === "event" ? b : undefined;
  };
  const b1 = root(pa.expression);
  if (b1) {
    checkEventUse(pa, b1, env);
    if (pa.name.text === "key") return eventField(pa, `${b1.leanVar}.key`, T.str, env, b1.site, null);
    fail(pa, `unsupported event property e.${pa.name.text} (supported: e.key, e.target.value, e.target.checked)`);
  }
  if (ts.isPropertyAccessExpression(pa.expression)) {
    const b2 = root(pa.expression.expression);
    const which = pa.expression.name.text;
    if (b2 && (which === "target" || which === "currentTarget")) {
      checkEventUse(pa, b2, env);
      if (pa.name.text === "value") return eventField(pa, `${b2.leanVar}.value`, T.str, env, b2.site, which);
      if (pa.name.text === "checked") return eventField(pa, `${b2.leanVar}.checked`, T.bool, env, b2.site, which);
      fail(pa, `unsupported event property (supported: e.target.value, e.target.checked)`);
    }
  }
  return null;
}

/** HTML elements whose `value` is a string (the IDL attribute; an `<li>`'s, `<meter>`'s or `<progress>`'s is a number). */
const STRING_VALUE_TAGS = ["input", "select", "textarea", "button", "option", "output", "data"];
/** The handler props React 18 dispatches a `SyntheticKeyboardEvent` to, whose `key` is always a string (`getEventKey`). */
const KEY_HANDLERS = ["onKeyDown", "onKeyUp", "onKeyPress"];

/**
 * Does JS read a string (`value`, `key`) or a boolean (`checked`) at this event field, as the
 * model's `DomEvent` says?  That depends on where the handler is attached, `site` — not on the
 * TypeScript type of the event parameter: React's handler types are bivariant
 * (`bivarianceHack`), so a handler annotated `(e: ChangeEvent<HTMLInputElement>)` is accepted
 * on a `<div>`, whose `value` is undefined, and `(e: KeyboardEvent<…>)` as an onChange, whose
 * event has no `key` (also for a handler passed by name).  `e.currentTarget` is the element
 * the handler is on; `e.target` is the element where the event happened, which is that element
 * only when nothing inside it can be an event target: an `<input>` (a void element), a
 * `<textarea>` (text only, and React reports a text node's event at its parent), and a
 * `<select>`'s onChange / onInput (`change` and `input` fire at the select; a click may be on
 * one of its options).
 */
function checkEventSite(pa: ts.PropertyAccessExpression, site: DomSite, which: "target" | "currentTarget" | null, field: string) {
  const on = `${site.prop} on <${site.tag}>`;
  if (field === "key") {
    if (!KEY_HANDLERS.includes(site.prop)) fail(pa, `\`${nodeText(pa)}\` is undefined in ${on}: only keyboard events (onKeyDown, onKeyUp, onKeyPress) have a key (React's handler types are bivariant, so TypeScript accepts a keyboard handler for any event)`);
    return;
  }
  if (!site.html) fail(pa, `\`${nodeText(pa)}\` in ${on}: this <${site.tag}> is inside an <svg> or <math> element, so React creates it as an SVG (MathML) element, which has no ${field}`);
  const self = site.tag === "input" || site.tag === "textarea" || (site.tag === "select" && (site.prop === "onChange" || site.prop === "onInput"));
  if (which === "target" && !self) {
    fail(pa, `\`${nodeText(pa)}\` in ${on}: e.target is the element where the event happened, which may be another element inside <${site.tag}> (with another ${field}, or none); put the handler on the control itself and read e.currentTarget.${field} there`);
  }
  if (field === "value" && !STRING_VALUE_TAGS.includes(site.tag)) {
    fail(pa, `\`${nodeText(pa)}\` is not a string in ${on}: only ${STRING_VALUE_TAGS.map((t) => `<${t}>`).join(", ")} have a string value (it is undefined on a <${site.tag}>${["li", "meter", "progress"].includes(site.tag) ? ", or a number" : ""}; React's handler types are bivariant, so TypeScript accepts a handler typed for another element)`);
  }
  if (field === "checked" && site.tag !== "input") {
    fail(pa, `\`${nodeText(pa)}\` is undefined in ${on}: only an <input> has checked (React's handler types are bivariant, so TypeScript accepts a handler typed for another element)`);
  }
}

/**
 * An event field, whose model (`DomEvent.value : JS.Str`, `.checked : Bool`, `.key : JS.Str`)
 * covers it only when JS reads a string (a boolean) there: TypeScript's type of the field must
 * say so (an `<li>`'s `value` is a number; a parameter annotated `any`), and so must the
 * element and the handler prop it is attached to (`checkEventSite`), which TypeScript's
 * bivariant handler types do not guarantee.
 */
function eventField(pa: ts.PropertyAccessExpression, code: string, t: VType, env: Env, site: DomSite, which: "target" | "currentTarget" | null): Val {
  const tt = env.m.checker.getTypeAtLocation(pa);
  const flag = t.k === "bool" ? ts.TypeFlags.BooleanLike : ts.TypeFlags.StringLike;
  const ok = tt.isUnion() ? tt.types.every((x) => x.flags & flag) : !!(tt.flags & flag);
  if (!ok) fail(pa, `\`${nodeText(pa)}\` is a ${env.m.checker.typeToString(tt)} here, not a ${t.k === "bool" ? "boolean" : "string"}: only an input's, select's or textarea's value (a string), a checkbox's checked and a key event's key are modelled`);
  checkEventSite(pa, site, which, pa.name.text);
  return { code, type: t };
}

/**
 * The event object is read while its handler runs: React 18 does not pool events, but it
 * sets `e.currentTarget` to null once the handler returns, and `e.target.value` /
 * `e.target.checked` read the live DOM element.  A function created inside the handler that
 * runs later — a functional update `setX(p => …)` (React calls it when it processes the
 * update, and again when it rebases it), a local helper — would read them then, not the
 * values the model gives the handler.  Only callbacks that run in place (array methods,
 * spec predicates) may read the event.
 */
function checkEventUse(node: ts.Node, b: Extract<Binding, { k: "event" }>, env: Env) {
  for (let n = node.parent; n && n !== b.fn; n = n.parent) {
    if ((ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && !isImmediateFn(n, env)) {
      fail(node, `\`${nodeText(node, 40)}\` is read inside ${laterWhat(n, env)}, which may run after React has dispatched the event: e.currentTarget is null then, and e.target.value / e.target.checked read the element's value at that time, not the one of this event. Read the event in the handler's own statements and use the copy: \`const v = ${nodeText(node, 40)};\` before the function`);
    }
  }
}

/** What kind of function created in a handler `fn` is, for messages. */
function laterWhat(fn: ts.ArrowFunction | ts.FunctionExpression, env: Env): string {
  let child: ts.Node = fn;
  while (ts.isParenthesizedExpression(child.parent)) child = child.parent;
  const p = child.parent;
  if (ts.isCallExpression(p) && ts.isIdentifier(p.expression)) {
    const s = symbolOf(env, p.expression);
    const b = s ? env.vars.get(s) : undefined;
    if (b?.k === "setter") return "a functional update (React calls it when it processes the update, and again when it rebases it onto other updates)";
  }
  return "a function created in the handler";
}

function fieldOf(base: Val, name: string, node: ts.Node, env: Env): Val {
  const m = env.m;
  const t = base.type;
  if (t.k === "arr" && name === "length") return { code: `(${paren(base.code)}.length : Int)`, type: T.int };
  if (t.k === "str" && name === "length") return { code: `(VReact.JS.strLen ${paren(base.code)})`, type: T.int };
  if (t.k === "map" && name === "size") return { code: `(VReact.JS.JSMap.size ${paren(base.code)})`, type: T.int };
  if (t.k === "set" && name === "size") return { code: `(VReact.JS.JSSet.size ${paren(base.code)})`, type: T.int };
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
  if (t.k === "tvar") {
    // a field constraint `T extends { readonly id: int }`: the accessor parameter of the field
    const f = t.fields?.find((f) => f.name === name);
    if (f) return { code: `(${f.acc} ${paren(base.code)})`, type: f.type };
    if (t.eq) {
      // (an equality constraint cannot be combined with a field constraint)
      fail(node, `\`${name}\` on a value of the type parameter ${t.name} is not supported: under an equality constraint the values of ${t.name} are abstract (the body is checked once, for every type ${t.name} may be): only ===, !==, includes, indexOf and distinct are available, no string or number properties or methods; compute \`${name}\` where the value has a concrete type and pass it as a parameter`);
    }
    fail(node, `\`${name}\` is not a field of the type parameter ${t.name}${t.fields ? ` (its constraint has ${t.fields.map((f) => f.name).join(", ")})` : ""}: values of a type parameter are abstract; declare the fields the function reads in its constraint: ${t.name} extends { readonly ${name}: … }`);
  }
  if (t.k === "tuple") fail(node, "use index access t[0] on tuples");
  if (t.k === "opt") fail(node, `\`${name}\` accessed on a possibly-null value: ${narrowAdvice(ts.isPropertyAccessExpression(node) ? node.expression : undefined, env)}`);
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
    return { code: tupleProj(base.code, i, n), type: base.type.elems[i] };
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

/**
 * The expected type `t` for an operand of an arithmetic operator, unless TypeScript types the
 * operand with a type parameter (`x + 1` on `x : T extends int`): then the operand keeps its own
 * type, and the operator rejects it (its values are abstract) instead of a type mismatch.
 */
function operandExpected(e: ts.Expression, env: Env, t: VType | undefined): VType | undefined {
  const tt = t && tsTypeOf(e, env);
  const isTP = (x: ts.Type) => (x.flags & ts.TypeFlags.TypeParameter) !== 0;
  return tt && (isTP(tt) || (tt.isUnion() && tt.types.some(isTP))) ? undefined : t;
}

function prefix(p: ts.PrefixUnaryExpression, env: Env, expected?: VType): Val {
  switch (p.operator) {
    case ts.SyntaxKind.ExclamationToken: {
      const v = boolOperand(p.operand, env);
      return { code: `(!${paren(v.code)})`, type: T.bool };
    }
    case ts.SyntaxKind.MinusToken: {
      if (ts.isNumericLiteral(p.operand)) {
        const v = expr(p.operand, env, numericExpected(expected));
        return { code: v.type.k === "int" ? leanInt(-BigInt(p.operand.text)) : `(-${v.code})`, type: v.type };
      }
      const v = expr(p.operand, env, operandExpected(p.operand, env, numericExpected(expected)));
      if (v.type.k === "tvar") fail(p, abstractMsg(v.type, "unary minus on"));
      if (!isNumeric(v.type)) fail(p, "unary minus on a non-number");
      return { code: `(-${paren(v.code)})`, type: v.type };
    }
    case ts.SyntaxKind.PlusToken: {
      // `+x` is ToNumber(x): the identity on numbers only (`+"5"` is 5, `+true` is 1)
      const v = expr(p.operand, env, operandExpected(p.operand, env, numericExpected(expected)));
      if (v.type.k === "tvar") fail(p, abstractMsg(v.type, "unary + on"));
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
    const l = boolOperand(b.left, env);
    const before = env.m.obCount();
    const r = boolOperand(b.right, env);
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
    if (isNullLit(stripParens(b.right), env)) return l;
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
    const le = l.type.elem;
    if (le.k === "map" || le.k === "set") {
      // `m.get(k) ?? []` outside an iteration is a Map/Set or an array in JS
      const r0 = stripParens(b.right);
      const rts = tsTypeOf(b.right, env);
      if (ts.isArrayLiteralExpression(r0) || (rts && (env.m.checker.isArrayType(rts) || env.m.checker.isTupleType(rts)))) {
        const ctor = le.k === "map" ? `new Map<${showType(le.key)}, ${showType(le.val)}>()` : `new Set<${showType(le.elem)}>()`;
        fail(b, `${nodeText(b, 40)} is a ${le.k === "map" ? "Map" : "Set"} or an array in JS: give a ${le.k === "map" ? "Map" : "Set"} as the default (${nodeText(b.left, 30)} ?? ${ctor}), or iterate it at once (new ${le.k === "map" ? "Map" : "Set"}(${nodeText(b.left, 30)} ?? []), [...(${nodeText(b.left, 30)} ?? [])])`);
      }
    }
    const r = expr(b.right, env, le);
    return { code: `(Option.getD ${paren(l.code)} ${paren(r.code)})`, type: le };
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
    if (l.type.k === "tvar") fail(b, abstractMsg(l.type, "an ordering comparison (<, <=, >, >=) on"));
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
    const l = expr(b.left, env, operandExpected(b.left, env, numericExpected(expected)));
    const r = expr(b.right, env, operandExpected(b.right, env, isNumeric(l.type) ? l.type : undefined));
    if (l.type.k === "str" || r.type.k === "str") {
      return { code: `(${concatPart(l, b.left, b)} ++ ${concatPart(r, b.right, b)})`, type: T.str };
    }
    return arith("+", l, r, b, env);
  }
  if (op === K.MinusToken || op === K.AsteriskToken) {
    const l = expr(b.left, env, operandExpected(b.left, env, numericExpected(expected)));
    const r = expr(b.right, env, operandExpected(b.right, env, isNumeric(l.type) ? l.type : undefined));
    return arith(op === K.MinusToken ? "-" : "*", l, r, b, env);
  }
  if (op === K.SlashToken) {
    let l = expr(b.left, env);
    let r = expr(b.right, env);
    const tv = l.type.k === "tvar" ? l.type : r.type.k === "tvar" ? r.type : null;
    if (tv) fail(b, abstractMsg(tv, "arithmetic (/) on"));
    // int / int is a JS number (no integer division); Math.floor(a / b) is handled at the call.
    l = coerce(l, T.num, b, env);
    // VTS values are JS values up to the sign of zero (an int 0 may be -0: `-x`, `a * b`,
    // `a % b`, … give -0), which only a division by a zero shows (1 / 0 is Infinity, 1 / -0 is
    // -Infinity): the divisor must not be zero (VReact/JS.lean, "Division")
    if (nonzeroLiteral(b.right, env)) {
      r = coerce(r, T.num, b, env);
      return { code: `(${paren(l.code)} / ${paren(r.code)})`, type: T.num };
    }
    const desc = `divisor ${nodeText(b.right)} is non-zero (1 / 0 is Infinity but 1 / -0 is -Infinity: VTS values do not keep the sign of zero)`;
    if (r.type.k === "int") {
      const ob = env.m.ob(b, "nonzero-divisor", desc);
      return { code: `(VReact.JS.Num.divInt ${paren(l.code)} ${paren(r.code)} ${ob})`, type: T.num };
    }
    r = coerce(r, T.num, b, env);
    const ob = env.m.ob(b, "nonzero-divisor", desc);
    return { code: `(VReact.JS.Num.divNum ${paren(l.code)} ${paren(r.code)} ${ob})`, type: T.num };
  }
  if (op === K.PercentToken) {
    const l = expr(b.left, env, operandExpected(b.left, env, T.int));
    const r = expr(b.right, env, operandExpected(b.right, env, T.int));
    const tv = l.type.k === "tvar" ? l.type : r.type.k === "tvar" ? r.type : null;
    if (tv) fail(b, abstractMsg(tv, "arithmetic (%) on"));
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
    if (!isNullLit(b.left, env) && !isNullLit(b.right, env)) fail(b, "use === / !== (loose equality is only allowed against null)");
  }
  if (!isNullLit(b.right, env) && !isNullLit(b.left, env)) return null;
  const lit = isNullLit(b.right, env) ? b.right : b.left;
  const other = isNullLit(b.right, env) ? b.left : b.right;
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

/** VTS types whose JS values are never null or undefined (all but options and void; type parameters are never instantiated with nullish types). */
function isPresentValue(t: VType): boolean {
  return ["bool", "int", "num", "str", "enum", "rec", "union", "arr", "tuple", "tvar", "map", "set"].includes(t.k);
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
  if (!sameType(l.type, r.type)) {
    const tv = tvarPart(l.type) ?? tvarPart(r.type);
    fail(b, `comparing ${showType(l.type)} with ${showType(r.type)}${tv ? ` (a value of the type parameter ${tv.name} is abstract: it can only be compared with another ${tv.name}, under an equality constraint)` : ""}`);
  }
  if (l.type.k !== "num" && !isPrimitiveEq(l.type)) {
    const t = l.type.k === "opt" ? l.type.elem : l.type;
    // (an optional operand shown with the nullish value TypeScript gives it: `m.get(k)` is
    // `V | undefined`, never null)
    const kl = nullishKinds(b.left, env);
    const optE = l.type.k === "opt" && !(kl && (kl.null || kl.undef)) ? b.right : b.left;
    const shown = showWithKinds(l.type, tsTypeOf(optE, env), env);
    if (t.k === "tvar") fail(b, noEqMsg(t, "==="));
    if (["rec", "arr", "union", "tuple"].includes(t.k)) fail(b, `=== on ${shown} compares object identity in JS; compare keys/fields instead`);
    if (t.k === "map" || t.k === "set") fail(b, `=== on ${shown} compares object identity in JS (a copy with the same entries is a different ${t.k === "map" ? "Map" : "Set"}); compare the contents instead (size, has, get, or the entries one by one)`);
    if (t.k === "num") {
      const k = nullishKinds(optE, env);
      const test = !k || (k.null && k.undef) ? "!= null" : k.undef ? "!== undefined" : "!== null";
      const what = nodeText(optE, 30);
      const simple = ts.isIdentifier(stripParens(optE)) || ts.isPropertyAccessExpression(stripParens(optE));
      fail(b, `=== on ${shown} is not supported: narrow it first (${simple ? `if (${what} ${test}) …` : `const v = ${what}; if (v ${test}) …`}), then compare the numbers`);
    }
    fail(b, `=== is not supported on ${shown}`);
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
  if (v.type.k === "tvar") fail(node, abstractMsg(v.type, "`+` (string concatenation) on"));
  if (v.type.k === "num") {
    fail(node, `\`+\` converts the number \`${nodeText(e, 30)}\` to a string with JS's Number::toString (shortest round-trip form), which VTS models only as an opaque function: use an int, or a template literal \`\${…}\` (where the conversion is opaque too)`);
  }
  if (v.type.k === "opt") fail(node, `\`${nodeText(e, 30)}\` may be null or undefined, which \`+\` would turn into the text "null" / "undefined": narrow it first`);
  return toStr(v, e);
}

/**
 * Whether `e` is statically a nonzero number: a numeric literal JS reads as nonzero (`2`, `0.5`,
 * `1e400`; not `1e-400`, which is 0), possibly negated or parenthesized, or a `const` initialised
 * with one (followed through imports). Such a divisor needs no obligation.
 */
function nonzeroLiteral(e: ts.Expression, env: Env, depth = 0): boolean {
  e = stripParens(e);
  if (ts.isNumericLiteral(e)) {
    const v = Number(e.text.replace(/_/g, ""));
    return !Number.isNaN(v) && v !== 0;
  }
  if (ts.isPrefixUnaryExpression(e) && (e.operator === ts.SyntaxKind.MinusToken || e.operator === ts.SyntaxKind.PlusToken)) return nonzeroLiteral(e.operand, env, depth);
  if (ts.isIdentifier(e) && depth < 8) {
    const d = resolved(env, symbolOf(env, e))?.valueDeclaration;
    if (d && ts.isVariableDeclaration(d) && d.initializer && ts.isVariableDeclarationList(d.parent) && (d.parent.flags & ts.NodeFlags.Const) && ts.isIdentifier(d.name)) {
      return nonzeroLiteral(d.initializer, env, depth + 1);
    }
  }
  return false;
}

function arith(op: string, l: Val, r: Val, node: ts.Node, env: Env): Val {
  const tv = l.type.k === "tvar" ? l.type : r.type.k === "tvar" ? r.type : null;
  if (tv) fail(node, abstractMsg(tv, `arithmetic (${op}) on`));
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
    // (`{ __proto__: v }` sets the prototype, it creates no property: ECMA-262 B.3.1)
    if ((ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) && propertyNameText(p.name) === "__proto__") fail(p, "a property `__proto__` is not supported in an object literal: `{ __proto__: v }` sets the object's prototype instead of creating a property");
    if (ts.isPropertyAssignment(p)) {
      if (ts.isComputedPropertyName(p.name) && !ts.isStringLiteralLike(p.name.expression)) fail(p.name, "computed property names are not supported in object literals: write the field name");
      if (props.has(propertyName(p.name))) fail(p.name, `${propertyName(p.name)} is given twice (JS keeps the last value)`);
      props.set(propertyName(p.name), p.initializer);
    }
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
  if (expected.k === "tvar") fail(o, `an object literal is not a value of the type parameter ${expected.name}: values of ${expected.name} come from the caller (parameters), they cannot be built in the generic function`);
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
      // an array, a Map / Set, or an iterator consumed here (`[...m.keys()]`)
      let v = iterated(el.expression, env, elemT ? T.arr(elemT) : undefined).v;
      if (v.type.k !== "arr") fail(el, "spread of a non-array");
      elemT = elemT ?? v.type.elem;
      v = coerce(v, T.arr(elemT), el, env);
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

/* ───────────────────────────── Map / Set ───────────────────────────── */

/** Methods returning an iterator: consumed at once (see `iterated`). */
const ITER_METHODS = new Set(["keys", "values", "entries"]);
const ITER_MSG = (what: string) =>
  `\`${what}\` is an iterator, which JS consumes once and which sees later changes of its Map/Set: use it at once — [...it], Array.from(it), for (… of it), new Map(it) / new Set(it) — and keep the resulting array`;
const ITERATE_MUTATE_MSG = (n: string) =>
  `\`${n}\` is mutated inside a for…of loop over it: JS visits the entries the loop adds (and skips those it deletes); iterate a copy instead: for (… of [...${n}])`;

/**
 * The list a JS iteration of `e` visits, where `e` is consumed at once (`[...e]`,
 * `Array.from(e)`, `for (… of e)`, `new Map(e)` / `new Set(e)`): an array (itself), a Map (its
 * entries `[k, v]`), a Set (its elements), or `m.keys()` / `m.values()` / `m.entries()` /
 * `s.values()` / `s.keys()` — in insertion order.  `coll`: the Map / Set itself when `e` visits
 * exactly its entries / elements (`new Map(m)` is a copy: the same value).
 */
function iterated(e: ts.Expression, env: Env, expectedArr?: VType): { v: Val; coll?: Val } {
  const m = env.m;
  const ck = m.checker;
  const e0 = stripParens(e);
  const kindOf = (x: ts.Expression) => collKindOf(x, env);
  const ofColl = (c: Val, at: ts.Expression, method: string | null): { v: Val; coll?: Val } => {
    const C = paren(c.code);
    if (c.type.k === "opt") fail(at, `\`${nodeText(at, 30)}\` may be null or undefined (iterating it throws in JS): narrow it first`);
    if (c.type.k === "map") {
      if (method === "keys") return { v: { code: `(VReact.JS.JSMap.keys ${C})`, type: T.arr(c.type.key) } };
      if (method === "values") return { v: { code: `(VReact.JS.JSMap.values ${C})`, type: T.arr(c.type.val) } };
      return { v: { code: `(VReact.JS.JSMap.entries ${C})`, type: T.arr({ k: "tuple", elems: [c.type.key, c.type.val] }) }, coll: c };
    }
    if (c.type.k === "set") {
      if (method === "entries") fail(at, "Set entries() (pairs [x, x]) is not supported: write [...s].map((x) => [x, x])");
      return { v: { code: `(VReact.JS.JSSet.elems ${C})`, type: T.arr(c.type.elem) }, coll: c };
    }
    return { v: c };
  };
  if (ts.isCallExpression(e0) && ts.isPropertyAccessExpression(e0.expression) && ITER_METHODS.has(e0.expression.name.text)) {
    const recvE = e0.expression.expression;
    const name = e0.expression.name.text;
    if (kindOf(recvE)) {
      if (e0.questionDotToken || e0.expression.questionDotToken) fail(e0, `\`${nodeText(e0, 30)}\` may be undefined (iterating it throws in JS): narrow the ${"receiver"} first`);
      arity(e0, name, 0, 0);
      return ofColl(expr(recvE, env), recvE, name);
    }
    const rt0 = tsTypeOf(recvE, env);
    const rt = rt0 && ck.getNonNullableType(rt0);
    if (rt && (ck.isArrayType(rt) || ck.isTupleType(rt))) fail(e0, `array iterators (keys/values/entries) are not modelled: use the array itself, or xs.map((x, i) => …) for the indices`);
  }
  if (kindOf(e0)) return ofColl(expr(e0, env), e0, null);
  // `o ?? fallback` with an optional Map/Set `o` (`new Set(m.get(k) ?? [])`, `[...(m.get(k) ?? [])]`):
  // JS iterates `o` when it is present, else the fallback (an iterable of the same elements);
  // with an empty array literal as the fallback it is a copy of `o` or an empty Map/Set
  if (ts.isBinaryExpression(e0) && e0.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken && kindOf(e0.left)) {
    const l = expr(e0.left, env);
    if (l.type.k === "opt" && (l.type.elem.k === "map" || l.type.elem.k === "set")) {
      const c = l.type.elem;
      const elemT: VType = c.k === "map" ? { k: "tuple", elems: [c.key, c.val] } : c.elem;
      const J = c.k === "map" ? "JSMap" : "JSSet";
      const listOf = c.k === "map" ? "VReact.JS.JSMap.entries" : "VReact.JS.JSSet.elems";
      const r0 = stripParens(e0.right);
      if (ts.isArrayLiteralExpression(r0) && r0.elements.length === 0) {
        const coll: Val = { code: `(Option.getD ${paren(l.code)} (VReact.JS.${J}.empty : ${leanType(c)}))`, type: c };
        return { v: { code: `(${listOf} ${coll.code})`, type: T.arr(elemT) }, coll };
      }
      const r = coerce(iterated(e0.right, env, T.arr(elemT)).v, T.arr(elemT), e0.right, env);
      return { v: { code: `(Option.getD (Option.map ${listOf} ${paren(l.code)}) ${paren(r.code)})`, type: T.arr(elemT) } };
    }
  }
  const v = expr(e0, env, expectedArr);
  if (v.type.k === "str" || v.type.k === "enum") {
    fail(e0, `iterating a string visits its code points (a character outside the BMP is one element), while VTS strings are UTF-16 code units: not modelled`);
  }
  return { v };
}

/**
 * `new Map(…)` / `new Set(…)`: empty (types from the type arguments or the expected type), a
 * copy of a Map / Set (the same value), or from an array or iteration of entries / elements
 * (`JSMap.ofList`: a duplicate key keeps its first position and takes its last value;
 * `JSSet.ofList`: first occurrences).
 */
function newCollection(ne: ts.NewExpression, env: Env, expected?: VType): Val {
  const m = env.m;
  const ck = m.checker;
  const tenv = m.prog.typeEnv;
  const kind = newKind(ne, ck, tenv);
  if (!kind) fail(ne, `\`new\` is only supported for Map and Set in VTS: ${nodeText(ne, 40)}`);
  const Name = kind === "map" ? "Map" : "Set";
  const J = kind === "map" ? "JSMap" : "JSSet";
  const params = kind === "map" ? "K, V" : "T";
  const args = ne.arguments ?? [];
  if (args.length > 1) fail(ne, `new ${Name}(…) takes at most one argument`);
  let t: VType | undefined;
  const ta = ne.typeArguments ?? [];
  if (ta.length) {
    if (kind === "map") {
      if (ta.length !== 2) fail(ne, `write new Map<K, V>(…) with both type arguments`);
      t = mapType(typeOfNode(ta[0], tenv, "MapKey"), typeOfNode(ta[1], tenv, "MapValue"), ne);
    } else {
      if (ta.length !== 1) fail(ne, `write new Set<T>(…) with one type argument`);
      t = setType(typeOfNode(ta[0], tenv, "SetItem"), ne);
    }
    checkValueType(ne, t, m.reg, `new ${Name}<…>`);
  } else {
    const exp = expected?.k === "opt" ? expected.elem : expected;
    if (exp?.k === kind) t = exp;
  }
  if (!t && kind === "map" && args.length === 1) t = literalPairsType(stripParens(args[0]), ne, env) ?? undefined;
  // without type arguments and a type to infer them from, TypeScript types it Map<any, any> /
  // Set<any> and checks nothing about what goes in (with an expected type, e.g. a `useState<T>`
  // argument, the translation types it, and checks the argument, at that type)
  const targs = collectionTypeArgs(ck.getTypeAtLocation(ne), ck);
  if (!t && (!targs || targs.some((a) => containsAny(a, ck)))) {
    fail(ne, `TypeScript types this \`${nodeText(ne, 30)}\` as ${Name}<${kind === "map" ? "any, any" : "any"}> (no type arguments, and nothing to infer them from), so it checks nothing about its ${kind === "map" ? "entries" : "elements"}: write new ${Name}<${params}>(…)`);
  }
  if (args.length === 0) {
    if (!t) fail(ne, `the type of this empty ${Name} is not known here: write new ${Name}<${params}>()`);
    return { code: `(VReact.JS.${J}.empty : ${leanType(t)})`, type: t };
  }
  const a = args[0];
  if (isNullLit(stripParens(a), env)) fail(a, `new ${Name}(${nodeText(a)}) is an empty ${Name}: write new ${Name}<${params}>()`);
  const elemOf = (x: VType): VType => (x.k === "map" ? { k: "tuple", elems: [x.key, x.val] } : (x as { elem: VType }).elem);
  const it = iterated(a, env, t ? T.arr(elemOf(t)) : undefined);
  if (it.coll && it.coll.type.k === kind) {
    // a copy: the same entries in the same order
    if (t && !sameType(it.coll.type, t)) fail(a, `type mismatch: expected ${showType(t)}, got ${showType(it.coll.type)}`);
    return { code: it.coll.code, type: it.coll.type };
  }
  const v = it.v;
  if (v.type.k !== "arr") fail(a, `new ${Name}(…) of a ${showType(v.type)} is not supported (only of an array, a Map, a Set, or their keys()/values()/entries())`);
  if (!t) {
    const el = v.type.elem;
    if (kind === "map") {
      if (el.k !== "tuple" || el.elems.length !== 2) fail(a, `new Map(…) takes [key, value] pairs (these elements are ${showType(el)}); with an array of pairs computed by a callback, give the types: new Map<K, V>(…)`);
      t = mapType(el.elems[0], el.elems[1], a);
    } else t = setType(el, a);
  }
  const w = coerce(v, T.arr(elemOf(t)), a, env);
  return { code: `(VReact.JS.${J}.ofList ${paren(w.code)})`, type: t };
}

/**
 * The type of `new Map(a)` without type arguments or an expected type, from its argument `a`
 * when that is built of `[key, value]` array literals.  TypeScript infers `Map<number, …>` for
 * `new Map([[1, "a"]])`, which cannot tell `int` from `number`, so VTS reads the types off the
 * pairs: a literal of pair literals takes the types of its first pair (`int` for an integer
 * literal, as in a `const`); pairs computed by a callback (`xs.map((x) => [x.id, x])`) are
 * rejected with the fix (their array literals would otherwise be read as arrays, not pairs).
 * Null for any other argument (a Map, entries, an array of tuples: their own types).
 */
function literalPairsType(a: ts.Expression, ne: ts.NewExpression, env: Env): VType | null {
  const NEED = `write the types: new Map<K, V>(…) (TypeScript infers number for an integer, which cannot tell int from number)`;
  if (ts.isArrayLiteralExpression(a)) {
    const pairs = a.elements.map(stripParens);
    if (!pairs.length || !pairs.every((p) => ts.isArrayLiteralExpression(p))) return null;
    const bad = pairs.find((p) => (p as ts.ArrayLiteralExpression).elements.length !== 2 || (p as ts.ArrayLiteralExpression).elements.some(ts.isSpreadElement));
    if (bad) fail(bad, `new Map(…) takes [key, value] pairs: this one has ${(bad as ts.ArrayLiteralExpression).elements.length === 2 ? "a spread" : `${(bad as ts.ArrayLiteralExpression).elements.length} elements`}`);
    const [k, v] = (pairs[0] as ts.ArrayLiteralExpression).elements;
    let kt: VType | undefined;
    let vt: VType | undefined;
    try {
      env.m.dryRun(() => {
        kt = expr(k, env).type;
        vt = expr(v, env).type;
      });
    } catch (err) {
      if (!(err instanceof VtsError)) throw err;
      fail(ne, `the types of this Map are not known from its first pair (${nodeText(pairs[0], 30)}): ${NEED}`);
    }
    return mapType(kt!, vt!, ne);
  }
  // pairs computed by a callback that returns an array literal
  const returnsArrayLiteral = (f: ts.Expression): boolean => {
    f = stripParens(f);
    if (!ts.isArrowFunction(f) && !ts.isFunctionExpression(f)) return false;
    if (!ts.isBlock(f.body)) return ts.isArrayLiteralExpression(stripParens(f.body));
    let found = false;
    const visit = (n: ts.Node) => {
      if (ts.isFunctionLike(n)) return;
      if (ts.isReturnStatement(n) && n.expression && ts.isArrayLiteralExpression(stripParens(n.expression))) found = true;
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(f.body, visit);
    return found;
  };
  if (ts.isCallExpression(a) && a.arguments.some(returnsArrayLiteral)) {
    fail(ne, `new Map(…) of [key, value] pairs computed by a callback: ${NEED}`);
  }
  return null;
}

/** A method call on a Map / Set value `c` (receiver expression `recvE`). */
function collectionMethod(name: string, c: Val, recvE: ts.Expression, call: ts.CallExpression, env: Env): Val {
  const args = call.arguments;
  const C = paren(c.code);
  const ck = env.m.checker;
  const t = c.type;
  if (t.k !== "map" && t.k !== "set") throw new Error("internal: not a collection");
  const isMap = t.k === "map";
  const Name = isMap ? "Map" : "Set";
  const J = isMap ? "JSMap" : "JSSet";
  const key = t.k === "map" ? t.key : t.elem;
  const what = recvText(recvE, 30);
  switch (name) {
    case "get":
      if (t.k !== "map") break;
      arity(call, "get", 1, 1);
      return { code: `(VReact.JS.JSMap.get ${C} ${paren(expr(args[0], env, key).code)})`, type: T.opt(t.val) };
    case "has":
      arity(call, "has", 1, 1);
      return { code: `(VReact.JS.${J}.has ${C} ${paren(expr(args[0], env, key).code)})`, type: T.bool };
    case "set":
    case "add": {
      if ((name === "set") !== isMap) break;
      // a pure update of a fresh copy (`new Map(m).set(k, v)`); anything else mutates a shared object
      if (!isFreshCollection(recvE, ck, env.m.prog.typeEnv)) {
        fail(call, `${what}.${name}(…) mutates ${what}: copy it first, new ${Name}(${what}).${name}(…), or call it as a statement on a fresh local copy (const n = new ${Name}(${what}); n.${name}(…);)`);
      }
      if (t.k === "map") {
        arity(call, "set", 2, 2);
        const k = expr(args[0], env, key);
        const v = expr(args[1], env, t.val);
        return { code: `(VReact.JS.JSMap.set ${C} ${paren(k.code)} ${paren(v.code)})`, type: t };
      }
      arity(call, "add", 1, 1);
      return { code: `(VReact.JS.JSSet.add ${C} ${paren(expr(args[0], env, key).code)})`, type: t };
    }
    case "delete":
    case "clear":
      fail(call, `${what}.${name}(…) mutates ${what} and returns ${name === "delete" ? "a boolean" : "undefined"}: VTS allows it only as a statement on a fresh local copy (const n = new ${Name}(${what}); n.${name}(…);)`);
    case "keys":
    case "values":
    case "entries":
      fail(call, ITER_MSG(nodeText(call, 40)));
    case "forEach":
      fail(call, `${Name}.forEach is not supported: write for (const ${isMap ? "[k, v]" : "x"} of ${what}) { … }`);
  }
  fail(call, `${Name} method ${name} is not modelled in VTS`);
}

/**
 * `n.set(k, v);` / `n.add(x);` / `n.delete(k);` / `n.clear();` on a fresh local Map / Set (allowed
 * by `checkCollectionMutation`): `n` is rebound to the updated value, as an assignment rebinds a
 * `let`.  The arguments are evaluated before the mutation (`n.set(k, n.size)` reads the old size).
 */
function mutateLocal(c: ts.CallExpression, callee: ts.PropertyAccessExpression, kind: "map" | "set", env: Env, rest: (e: Env) => string): string {
  const name = callee.name.text;
  const recv = stripParens(callee.expression);
  const Name = kind === "map" ? "Map" : "Set";
  const J = kind === "map" ? "JSMap" : "JSSet";
  const s = ts.isIdentifier(recv) ? symbolOf(env, recv) : undefined;
  const b = s ? env.vars.get(s) : undefined;
  if (!ts.isIdentifier(recv) || !s?.valueDeclaration || !freshMutable.has(s.valueDeclaration) || b?.k !== "val" || b.type.k !== kind) {
    const what = recvText(recv, 30);
    fail(c, `${what}.${name}(…) mutates ${what}: only a local const initialised with new ${Name}(…) in this function (a fresh copy nothing else refers to) may be mutated; copy first: const n = new ${Name}(${what}); n.${name}(…);`);
  }
  const t = b.type;
  const key = t.k === "map" ? t.key : (t as { elem: VType }).elem;
  const args = c.arguments;
  const X = paren(b.code);
  let code: string;
  if (name === "clear") {
    arity(c, "clear", 0, 0);
    code = `(VReact.JS.${J}.empty : ${leanType(t)})`;
  } else if (name === "delete") {
    arity(c, "delete", 1, 1);
    code = `(VReact.JS.${J}.delete ${X} ${paren(expr(args[0], env, key).code)})`;
  } else if (name === "set" && t.k === "map") {
    arity(c, "set", 2, 2);
    const k = expr(args[0], env, key);
    const v = expr(args[1], env, t.val);
    code = `(VReact.JS.JSMap.set ${X} ${paren(k.code)} ${paren(v.code)})`;
  } else if (name === "add" && t.k === "set") {
    arity(c, "add", 1, 1);
    code = `(VReact.JS.JSSet.add ${X} ${paren(expr(args[0], env, key).code)})`;
  } else fail(c, `${Name} has no method ${name}`);
  const { env: e1, name: ln } = freshLocal(forgetNarrowing(env, s), leanIdent(recv.text));
  return `(let ${ln}${letType(t)} := ${code!};\n${rest(bind(e1, s, { k: "val", code: ln, type: t }))})`;
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
  // (Lean checks the callback for any value of its parameters: `generalized`)
  const { env: e2, binders, typed } = lambdaParams(fn, { ...env, generalized: "an array-method callback: Lean checks it for every value of its parameters, not only the array's elements (and the program's accumulators or indexes)" }, paramTypes, paramTs);
  const before = env.m.obCount();
  // (a predicate's result is tested for truthiness by JS: `xs.filter((x) => x)`)
  const body = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, e2, expectedRet, fn) : expectedRet?.k === "bool" ? boolOperand(fn.body, e2) : expr(fn.body, e2, expectedRet);
  return { binders, typed, body, obligations: env.m.obCount() > before, env: e2 };
}

/**
 * A contract lambda `(x₁, …) => c` (`callbackRequires`): JS never calls it, it states that `c`
 * holds (is truthy) for the arguments of every call of the callback.  An expression body is
 * read as a contract proposition (`prop`: the consequent of `implies(a, b)`, the right operand
 * of `&&`, … under their guards, as in `requires`); a block body is read as code, its
 * obligations checked for every value of the parameters.
 */
export function contractLambda(
  fn: ts.ArrowFunction | ts.FunctionExpression,
  env: Env,
  paramTypes: VType[],
  paramTs?: readonly (ts.Type | null | undefined)[],
): { binders: string[]; typed: string[]; prop: string } {
  const { env: e2, binders, typed } = lambdaParams(fn, { ...env, generalized: "a callbackRequires contract: Lean checks it for every value of the callback's parameters" }, paramTypes, paramTs);
  if (ts.isBlock(fn.body)) return { binders, typed, prop: `${paren(valueBlock(fn.body.statements, e2, T.bool, fn).code)} = true` };
  return { binders, typed, prop: prop(fn.body, e2) };
}

/** Bind the parameters of an inline function to fresh Lean variables (`_` for the arguments it ignores). */
function lambdaParams(
  fn: ts.ArrowFunction | ts.FunctionExpression,
  env: Env,
  paramTypes: VType[],
  paramTs?: readonly (ts.Type | null | undefined)[],
): { env: Env; binders: string[]; typed: string[] } {
  let e2 = env;
  const binders: string[] = [];
  const typed: string[] = [];
  fn.parameters.forEach((p, i) => {
    const t = paramTypes[i];
    checkNotThisParam(p);
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
  return { env: e2, binders, typed };
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
  if (ts.isParameter(p)) checkNotThisParam(p);
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
    // (a field-constrained type parameter: its constrained fields, through their accessors)
    if (t.k !== "rec" && !(t.k === "tvar" && t.fields)) fail(name, "destructuring is only supported for record types");
    const { env: e1, name: ln } = freshLocal(env, "o");
    let e2 = e1;
    for (const el of name.elements) {
      if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) fail(el, "only simple destructuring { a, b } is supported");
      const fname = el.propertyName ? propertyName(el.propertyName) : el.name.text;
      const v = fieldOf({ code: ln, type: t }, fname, el, env);
      e2 = bind(e2, symbolOf(env, el.name)!, { k: "val", code: v.code, type: v.type });
    }
    return { env: e2, binder: ln };
  }
  if (ts.isArrayBindingPattern(name)) {
    // `([k, v]) => …`, `for (const [k, v] of m)`: the components of a tuple; a shorter pattern
    // binds a prefix (`([k]) => k`: JS leaves the other elements unbound), a longer one is
    // rejected (JS would bind `undefined` to the extra names)
    if (t.k !== "tuple") fail(name, `array destructuring is only supported on tuples (this value is a ${showType(t)})`);
    const n = t.elems.length;
    if (name.elements.length > n) fail(name, `the tuple ${showType(t)} has only ${n} elements, but this pattern names ${name.elements.length} (JS would bind undefined to the extra ones): destructure at most ${n}`);
    const { env: e1, name: ln } = freshLocal(env, "tup");
    let e2 = e1;
    name.elements.forEach((el, i) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) fail(el, "only simple tuple destructuring [a, b] is supported (no default values, rest elements or nested patterns)");
      e2 = bind(e2, symbolOf(env, el.name)!, { k: "val", code: tupleProj(ln, i, n), type: t.elems[i] });
    });
    return { env: e2, binder: ln };
  }
  fail(name, "unsupported parameter pattern");
}

/** Component `i` of an `n`-tuple `x` (`A × B × C` is right-nested: `x.2.1` is the second). */
function tupleProj(x: string, i: number, n: number): string {
  let code = paren(x);
  for (let j = 0; j < i; j++) code = `${code}.2`;
  if (i < n - 1) code = `${code}.1`;
  return code;
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
      if (info.tparams.length) return genericCall(info, c, env, expected);
      const as = args.map((a, i) => paren(expr(a, env, info.params[i].type).code));
      const ob = info.hasPre ? " " + m.ob(c, "precondition", `precondition of ${info.name}(${args.map((a) => argText(a)).join(", ")})`) : "";
      m.deps.add(info.qname);
      return { code: `(${info.qname}${as.map((a) => " " + a).join("")}${ob})`, type: info.ret };
    }
    if (isGlobal(env, callee, "String") && args.length === 1) return { code: toStr(expr(args[0], env), args[0]), type: T.str };
    fail(c, `call to \`${callee.text}\` is not supported (only verified top-level functions, local helper arrows, and modelled library methods)`);
  }
  if (ts.isPropertyAccessExpression(callee)) {
    const mname = callee.name.text;
    const objE = callee.expression;
    // Math.*
    if (isGlobal(env, objE, "Math")) return mathCall(mname, c, env, expected);
    // Array.from(it): an array of what `it` iterates (the library's Array, not a user binding)
    if (mname === "from" && isGlobal(env, objE, "Array") && isLibSymbol(resolved(env, symbolOf(env, objE)), m.prog.typeEnv)) {
      arity(c, "Array.from", 1, 1, "a mapping function is not supported: write Array.from(x).map((y) => …)");
      const v = iterated(args[0], env, expected?.k === "arr" ? expected : undefined).v;
      if (v.type.k !== "arr") fail(args[0], `Array.from of a ${showType(v.type)} is not supported (only arrays, Maps, Sets and their keys()/values()/entries())`);
      return v;
    }
    if (ts.isIdentifier(objE) && objE.text === "props") {
      const s = symbolOf(env, objE);
      if (s && env.vars.get(s)?.k === "props") fail(c, "callbacks can only be invoked as statements inside an event handler");
    }
    // an iterator (`m.keys()`, `s.values()`, …) is only consumed at once (see `iterated`)
    if (ITER_METHODS.has(mname)) {
      const rt0 = tsTypeOf(objE, env);
      const rt = rt0 && m.checker.getNonNullableType(rt0);
      if (rt && (collectionKind(rt, m.prog.typeEnv) || m.checker.isArrayType(rt) || m.checker.isTupleType(rt))) fail(c, ITER_MSG(nodeText(c, 40)));
    }
    const obj = expr(objE, env);
    if (obj.type.k === "arr") return arrayMethod(mname, obj, c, env, expected);
    if (obj.type.k === "str") return stringMethod(mname, obj, c, env);
    if (obj.type.k === "map" || obj.type.k === "set") return collectionMethod(mname, obj, objE, c, env);
    if (obj.type.k === "opt") fail(c, `method call on a possibly-null value: ${narrowAdvice(objE, env)}`);
    if (obj.type.k === "tvar") fail(c, abstractMsg(obj.type, `calling the method ${mname} on`));
    fail(c, `method ${mname} not supported on ${showType(obj.type)}`);
  }
  fail(c, `unsupported call ${nodeText(c)}`);
}

/**
 * The VTS type of a parameter or result annotation of a local helper that is inlined at a call:
 * the argument (result) is bound as data, so a function or React node type, which has no Lean
 * value type, is rejected (a helper used as an event handler, whose parameter is the event, is
 * not inlined this way).
 */
function helperValueType(t: ts.TypeNode, env: Env, hint: string, what: string): VType {
  const vt = typeOfNode(t, env.m.prog.typeEnv, hint);
  checkValueType(t, vt, env.m.reg, what);
  return vt;
}

/* ─────────────────────────── generic calls ─────────────────────────── */

type TVarT = VType & { k: "tvar" };

/**
 * A call of a generic top-level function: its type arguments (explicit `f<int>(…)`, or inferred
 * from the arguments' VTS types — TypeScript's inference cannot tell `int` from `number`), checked
 * against the constraints, then `(f (T := X) … accessors … args … [h_pre])`: the type arguments by
 * name, the accessor of each constrained field as a function, the arguments at the instantiated
 * parameter types (which `coerce` widens to).
 */
function genericCall(info: FnInfo, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const m = env.m;
  const args = c.arguments;
  const σ = inferTypeArgs(info, c, env, expected);
  checkInstantiation(info, σ, c, env);
  checkGenericArgKinds(info, c, env);
  const targs = info.tparams.map((p) => `(${p.lean} := ${leanType(σ.get(p.id)!)})`);
  const accs = info.tparams.flatMap((p) => (p.fields ?? []).map((f) => accessorArg(σ.get(p.id)!, f, c, env)));
  const as = args.map((a, i) => paren(expr(a, env, substType(info.params[i].type, σ)).code));
  const ob = info.hasPre ? m.ob(c, "precondition", `precondition of ${info.name}(${args.map((a) => argText(a)).join(", ")})`) : null;
  m.deps.add(info.qname);
  const parts = [...targs, ...accs, ...as, ...(ob ? [ob] : [])];
  return { code: `(${info.qname} ${parts.join(" ")})`, type: substType(info.ret, σ) };
}

/** An argument whose type comes from its context (the parameter type), not from itself. */
function needsContext(e: ts.Expression, env: Env): boolean {
  e = stripParens(e);
  if (isNullLit(e, env) || ts.isStringLiteralLike(e) || ts.isObjectLiteralExpression(e)) return true;
  if (ts.isArrayLiteralExpression(e)) return e.elements.every((x) => !ts.isSpreadElement(x) && needsContext(x, env));
  if (ts.isConditionalExpression(e)) return needsContext(e.whenTrue, env) && needsContext(e.whenFalse, env);
  return false;
}

/**
 * The instantiation of a generic function's type parameters at a call (by id): the explicit type
 * arguments, or by unification of the declared parameter types with the arguments' VTS types —
 * first the arguments that have a type of their own, then the result type with the type the
 * context expects (for type parameters still open: `const xs: readonly int[] = empty()`), then
 * the arguments that take their type from the parameter (`null`, `[]`, literals) — joining
 * where JS values fit both (`int` and `number` give `number`, an enum and a string `string`).
 */
function inferTypeArgs(info: FnInfo, c: ts.CallExpression, env: Env, expected?: VType): Map<number, VType> {
  const σ = new Map<number, VType>();
  const own = new Set(info.tparams.map((p) => p.id));
  const names = info.tparams.map((p) => p.name).join(", ");
  if (c.typeArguments?.length) {
    if (c.typeArguments.length !== info.tparams.length) fail(c, `${info.name} has the type parameters ${names}: pass all of them (${info.name}<…>(…)) or none`);
    c.typeArguments.forEach((ta, i) => σ.set(info.tparams[i].id, typeOfNode(ta, env.m.prog.typeEnv, capitalize(info.name) + capitalize(info.tparams[i].name))));
    return σ;
  }
  const args = c.arguments;
  const conflict = (p: TVarT, x: VType, y: VType): never =>
    fail(c, `cannot infer the type parameter ${p.name} of ${info.name}: the arguments give it the types ${showType(x)} and ${showType(y)}; write ${info.name}<…>(…) with the type you mean`);
  const later: { pt: VType; arg: ts.Expression }[] = [];
  // the errors of arguments that have a type of their own but could not be typed: when a type
  // parameter their parameter type mentions stays open, that error is the problem, not the
  // inference (not for `[]`, `null`, literals: typed by their parameter, they need it)
  const argErrors: { pt: VType; err: VtsError }[] = [];
  const tryType = (pt: VType, arg: ts.Expression, record: boolean): VType | null => {
    try {
      return typeOf(arg, env);
    } catch (e) {
      if (!(e instanceof VtsError)) throw e;
      if (record) argErrors.push({ pt, err: e });
      return null;
    }
  };
  const first = (pt: VType, arg: ts.Expression) => {
    if (!mentionsTVar(pt, own)) return;
    const a = stripParens(arg);
    // a tuple literal: element by element (as an array literal it would have one element type)
    if (pt.k === "tuple" && ts.isArrayLiteralExpression(a) && a.elements.length === pt.elems.length && !a.elements.some(ts.isSpreadElement)) {
      a.elements.forEach((el, j) => first(pt.elems[j], el));
      return;
    }
    const at = needsContext(a, env) ? null : tryType(pt, a, true);
    if (at) unify(pt, at, σ, own, conflict);
    else later.push({ pt, arg: a });
  };
  for (let i = 0; i < args.length; i++) first(info.params[i].type, args[i]);
  if (expected && expected.k !== "void" && expected.k !== "unit" && info.tparams.some((p) => !σ.has(p.id)) && mentionsTVar(info.ret, own)) {
    // (only for the type parameters the arguments left open; a mismatch is reported where the result is used)
    const σ2 = new Map(σ);
    try {
      // (a `T` result where `X | null` is expected: T = X, the result is widened)
      unify(info.ret, info.ret.k === "tvar" && expected.k === "opt" ? expected.elem : expected, σ2, own, conflict);
      for (const [k, v] of σ2) if (!σ.has(k)) σ.set(k, v);
    } catch (e) {
      if (!(e instanceof VtsError)) throw e;
    }
  }
  for (const { pt, arg } of later) {
    const partial = substType(pt, σ);
    if (!mentionsTVar(partial, own)) {
      // typed at the instantiated parameter type below, if it fits there (`"z"` where `T` is an
      // enum without that member: then by its own type, joined: T = string)
      try {
        typeOf(arg, env, partial);
        continue;
      } catch (e) {
        if (!(e instanceof VtsError)) throw e;
      }
    }
    const at = tryType(pt, arg, false);
    if (at) unify(pt, at, σ, own, conflict);
  }
  const open = info.tparams.filter((p) => !σ.has(p.id));
  // (an argument's own error, e.g. `xs.toSorted()` without a comparator, explains why the type
  // parameter it would have given is open)
  const blame = argErrors.find((x) => open.some((p) => mentionsTVar(x.pt, new Set([p.id]))));
  if (blame) throw blame.err;
  if (open.length) {
    const s = open.length > 1 ? "s" : "";
    fail(c, `cannot infer the type parameter${s} ${open.map((p) => p.name).join(", ")} of ${info.name} from the arguments${expected ? "" : " (nor from the type the result must have)"}: write ${info.name}<${info.tparams.map((p) => (σ.has(p.id) ? showType(σ.get(p.id)!) : p.name)).join(", ")}>(…) with the type${s} you mean`);
  }
  return σ;
}

/** Bind the callee's type parameters (`own`) in `p` so that it fits a value of type `a`. */
function unify(p: VType, a: VType, σ: Map<number, VType>, own: ReadonlySet<number>, conflict: (p: TVarT, x: VType, y: VType) => never): void {
  if (p.k === "tvar" && own.has(p.id)) {
    const cur = σ.get(p.id);
    if (!cur) {
      σ.set(p.id, a);
      return;
    }
    const j = joinTypes(cur, a);
    if (!j) conflict(p, cur, a);
    σ.set(p.id, j);
    return;
  }
  if (p.k === "arr" && a.k === "arr") return unify(p.elem, a.elem, σ, own, conflict);
  if (p.k === "opt") return unify(p.elem, a.k === "opt" ? a.elem : a, σ, own, conflict);
  if (p.k === "tuple" && a.k === "tuple" && p.elems.length === a.elems.length) p.elems.forEach((e, i) => unify(e, a.elems[i], σ, own, conflict));
  // Map / Set: their keys, values and elements (`ReadonlyMap<K, V>` with a `ReadonlyMap<int, Order>`
  // argument: K = int, V = Order; VTS has no Map/Set covariance, so the argument must then have
  // exactly the instantiated type, which `coerce` checks)
  if (p.k === "map" && a.k === "map") {
    unify(p.key, a.key, σ, own, conflict);
    unify(p.val, a.val, σ, own, conflict);
  }
  if (p.k === "set" && a.k === "set") unify(p.elem, a.elem, σ, own, conflict);
  // (other shapes: nothing to infer; the argument is checked against the instantiated type)
}

/** The least VTS type both types widen to (TypeScript's inference of a type parameter from both), or null. */
function joinTypes(x: VType, y: VType): VType | null {
  if (sameType(x, y)) return x;
  if (isNumeric(x) && isNumeric(y)) return T.num;
  if ((x.k === "enum" || x.k === "str") && (y.k === "enum" || y.k === "str")) return T.str;
  if (x.k === "arr" && y.k === "arr") {
    const e = joinTypes(x.elem, y.elem);
    return e && T.arr(e);
  }
  if (x.k === "opt" || y.k === "opt") {
    const e = joinTypes(x.k === "opt" ? x.elem : x, y.k === "opt" ? y.elem : y);
    return e && T.opt(e);
  }
  if (x.k === "tuple" && y.k === "tuple" && x.elems.length === y.elems.length) {
    const es = x.elems.map((e, i) => joinTypes(e, y.elems[i]));
    return es.every((e) => e) ? { k: "tuple", elems: es as VType[] } : null;
  }
  return null;
}

/** The type of the field `name` of values of type `t` (a record field, a union's tag or shared field, a constrained field), or null. */
function fieldTypeOf(t: VType, name: string, env: Env): VType | null {
  const reg = env.m.reg;
  if (t.k === "rec") return reg.rec(t).find((f) => f.name === name)?.type ?? null;
  if (t.k === "union") {
    const u = reg.union(t);
    if (name === u.tag) return T.str;
    return sharedFields(u.variants).find((f) => f.name === name)?.type ?? null;
  }
  if (t.k === "tvar") return t.fields?.find((f) => f.name === name)?.type ?? null;
  return null;
}

/** The TypeScript type of the field `name` of values of type `t` (its null/undefined kinds), or null. */
function fieldTsTypeOf(t: VType, name: string, env: Env): ts.Type | null {
  const ck = env.m.checker;
  if (t.k === "tvar") return env.m.reg.tparamById.get(t.id)?.fieldTs.get(name) ?? null;
  if (t.k !== "rec" && t.k !== "union") return null;
  const nt: NamedType = env.m.reg.get(t.name);
  const d = nt.decl;
  if (!d) return null;
  const tt = ts.isTypeAliasDeclaration(d) || ts.isInterfaceDeclaration(d) ? ck.getTypeAtLocation(d.name) : ts.isTypeNode(d) ? ck.getTypeFromTypeNode(d) : null;
  const sym = tt && ck.getPropertyOfType(tt, name);
  return sym ? ck.getTypeOfSymbol(sym) : null;
}

/**
 * The instantiation must be a closed value type that is never null or undefined (JS has one
 * nullish value, where `T | null` with `T = X | null` would be `Option (Option X)` in Lean), a type
 * JS compares by value for an equality constraint (never `number`: TypeScript cannot tell it from
 * `int`), and have each constrained field at exactly its type and nullish kind.
 */
function checkInstantiation(info: FnInfo, σ: Map<number, VType>, c: ts.CallExpression, env: Env) {
  const ck = env.m.checker;
  info.tparams.forEach((p, i) => {
    const t = σ.get(p.id)!;
    // (shown with the nullish values TypeScript gives it: from the explicit type argument
    // `size<int | undefined>(…)`, or else from the argument it comes from, `int | undefined`)
    const explicit = c.typeArguments?.[i];
    const tt = explicit ? ck.getTypeFromTypeNode(explicit) : tsTypeAtTVar(info, p.id, c, env);
    const at = `${info.name}: its type parameter ${p.name} would be ${showWithKinds(t, tt, env)}`;
    if (t.k === "opt") {
      const k = tt ? kindsOfType(tt) : null;
      const nullish = k && k.undef && !k.null ? "undefined" : "null";
      const why = `a type parameter is never instantiated with a nullable type (JS has one nullish value, while ${p.name} | ${nullish} would nest two in the model)`;
      fail(c, explicit
        ? `${at}, which includes null/undefined: ${why}; write a type argument without null/undefined (e.g. ${info.name}<${info.tparams.map((q, j) => (j === i ? showType(t.elem) : q.name)).join(", ")}>(…)), or give ${info.name} a parameter of type ${p.name} | ${nullish}`
        : `${at}, which includes null/undefined: ${why}; pass present values, or give ${info.name} a parameter of type ${p.name} | ${nullish}`);
    }
    if (t.k === "void" || t.k === "unit" || t.k === "fn" || t.k === "node") fail(c, `${at}, which is not a value type`);
    const np = nonValuePart(t, env.m.reg);
    if (np) fail(c, `${at}, which has ${np}: not data (functions are not first-class in VTS, and React nodes are only rendered)`);
    if (p.eq && !isEqType(t)) {
      fail(c, t.k === "num"
        ? `${at}: ${p.name} has an equality constraint, and number has no usable equality (NaN !== NaN, and SameValueZero equates -0 and 0); use int`
        : `${at}: ${p.name} has an equality constraint, so its values must be booleans, ints, strings or string-literal enums (JS compares ${showType(t)} values by identity)`);
    }
    for (const f of p.fields ?? []) {
      const ft = fieldTypeOf(t, f.name, env);
      if (!ft) {
        const where = t.k === "union" ? ` (it must be a field of every variant)` : "";
        fail(c, `${at}, which has no field ${f.name}${where}, but ${p.name} extends { ${f.name}: ${showType(f.type)} }`);
      }
      if (!sameType(ft, f.type)) fail(c, `${at}: its field ${f.name} has the type ${showType(ft)}, and the constraint of ${p.name} says ${showType(f.type)} (they must be the same type)`);
      if (hasOptPart(f.type)) {
        const want = p.fieldTs.get(f.name);
        const got = fieldTsTypeOf(t, f.name, env);
        const a = want && nullShape(want, f.type, ck);
        const b = got && nullShape(got, ft, ck);
        if (a == null || b == null || a !== b) {
          fail(c, `${at}: its field ${f.name} is not null/undefined exactly as the constraint of ${p.name} says (${want ? ck.typeToString(want) : "?"} vs. ${got ? ck.typeToString(got) : "?"}); null and undefined are different JS values`);
        }
      }
    }
  });
}

/**
 * The TypeScript type of the part of an argument that the type parameter `id` matches (the first
 * argument whose parameter type mentions it there, through arrays, options and tuples), or null.
 */
function tsTypeAtTVar(info: FnInfo, id: number, c: ts.CallExpression, env: Env): ts.Type | null {
  const ck = env.m.checker;
  const at = (pt: VType, t: ts.Type | null): ts.Type | null => {
    if (!t) return null;
    switch (pt.k) {
      case "tvar":
        return pt.id === id ? t : null;
      case "arr":
        return at(pt.elem, ck.getIndexTypeOfType(t, ts.IndexKind.Number) ?? null);
      case "opt":
        return at(pt.elem, ck.getNonNullableType(t));
      case "tuple": {
        if (!ck.isTupleType(t)) return null;
        const xs = ck.getTypeArguments(t as ts.TypeReference);
        for (let i = 0; i < pt.elems.length; i++) {
          const r = at(pt.elems[i], xs[i] ?? null);
          if (r) return r;
        }
        return null;
      }
      case "map":
      case "set": {
        const xs = collectionTypeArgs(ck.getNonNullableType(t), ck);
        const parts = pt.k === "map" ? [pt.key, pt.val] : [pt.elem];
        if (!xs || xs.length !== parts.length) return null;
        for (let i = 0; i < parts.length; i++) {
          const r = at(parts[i], xs[i]);
          if (r) return r;
        }
        return null;
      }
      default:
        return null;
    }
  };
  for (let i = 0; i < c.arguments.length && i < info.params.length; i++) {
    const r = at(info.params[i].type, tsTypeOf(c.arguments[i], env));
    if (r) return r;
  }
  return null;
}

/**
 * TypeScript absorbs a nullish argument into a type parameter (`x: T | null` takes an
 * `int | undefined`, with T = `number | undefined`), while the instantiation is never nullish:
 * where a parameter type has optional parts, the argument's must be null/undefined exactly as
 * the declaration says (the generic body was checked with those).
 */
function checkGenericArgKinds(info: FnInfo, c: ts.CallExpression, env: Env) {
  const ck = env.m.checker;
  c.arguments.forEach((a, i) => {
    const pt = info.params[i].type;
    if (!hasOptPart(pt)) return;
    const declNode = info.decl.parameters[i]?.type;
    const real = tsTypeOf(a, env);
    if (declNode && real && nullishWithin(real, ck.getTypeFromTypeNode(declNode), pt, ck)) return;
    const has = real ? `\`${ck.typeToString(real)}\`` : "a value whose TypeScript type does not say whether it is null or undefined";
    fail(a, `the argument \`${nodeText(a, 40)}\` is ${has}, but the parameter ${info.params[i].name} of ${info.name} is \`${declNode ? nodeText(declNode, 40) : showType(pt)}\`: null and undefined are different JS values, and the generic function was checked for the one its parameter type names; convert the argument first (e.g. x ?? null), or annotate it exactly`);
  });
}

/**
 * At every optional position of `vt`, may a value of TypeScript type `a` be nullish only as one of
 * type `d` (a present value fits everywhere)?  False when unknown (`any`, `unknown`).
 */
function nullishWithin(a: ts.Type, d: ts.Type, vt: VType, ck: ts.TypeChecker): boolean {
  switch (vt.k) {
    case "opt": {
      const ka = kindsOfType(a);
      const kd = kindsOfType(d);
      if (!ka || !kd || (ka.null && !kd.null) || (ka.undef && !kd.undef)) return false;
      return nullishWithin(ck.getNonNullableType(a), ck.getNonNullableType(d), vt.elem, ck);
    }
    case "arr": {
      const ea = ck.getIndexTypeOfType(a, ts.IndexKind.Number);
      const ed = ck.getIndexTypeOfType(d, ts.IndexKind.Number);
      return !!ea && !!ed && nullishWithin(ea, ed, vt.elem, ck);
    }
    case "tuple": {
      if (!ck.isTupleType(a) || !ck.isTupleType(d)) return false;
      const xa = ck.getTypeArguments(a as ts.TypeReference);
      const xd = ck.getTypeArguments(d as ts.TypeReference);
      return xa.length === vt.elems.length && xd.length === vt.elems.length && vt.elems.every((e, i) => nullishWithin(xa[i], xd[i], e, ck));
    }
    case "map":
    case "set": {
      // (keys and elements are never optional; a Map value may have optional parts:
      // `ReadonlyMap<K, readonly (V | null)[]>`)
      const parts = vt.k === "map" ? [vt.key, vt.val] : [vt.elem];
      if (!parts.some(hasOptPart)) return true;
      const xa = collectionTypeArgs(a, ck);
      const xd = collectionTypeArgs(d, ck);
      return !!xa && !!xd && xa.length === parts.length && xd.length === parts.length && parts.every((e, i) => nullishWithin(xa[i], xd[i], e, ck));
    }
    default:
      // (no optional part at this position; a type parameter's value is never nullish)
      return true;
  }
}

/** The accessor function passed for the constrained field `f` of an instantiation `t`. */
function accessorArg(t: VType, f: TField, c: ts.CallExpression, env: Env): string {
  const x = env.m.fresh("x");
  const v = fieldOf({ code: x, type: t }, f.name, c, env);
  return `(fun (${x} : ${leanType(t)}) => ${v.code})`;
}

function inlineClosure(b: Extract<Binding, { k: "closure" }>, c: ts.CallExpression, env: Env, expected?: VType): Val {
  const fn = b.fn;
  checkPlainParams(fn.parameters, `the local function ${nodeText(c.expression, 30)}`);
  if (fn.parameters.length !== c.arguments.length) fail(c, "arity mismatch");
  // Evaluate the arguments in the caller env, bind them in the closure's env.
  let lets = "";
  let e2: Env = { ...b.env, scope: env.scope, narrow: b.env.narrow, curState: env.curState, generalized: env.generalized ?? b.env.generalized };
  fn.parameters.forEach((p, i) => {
    if (!p.type) fail(p, "helper function parameters need type annotations");
    const t = helperValueType(p.type, env, "Arg", `parameter \`${p.name.getText()}\` of ${nodeText(c.expression, 30)}`);
    const a = expr(c.arguments[i], env, t);
    const r = bindParam(p.name, t, e2, "declared");
    e2 = r.env;
    lets += `let ${r.binder} := ${a.code}; `;
  });
  const retT = fn.type ? helperValueType(fn.type, env, "Ret", `the result of ${nodeText(c.expression, 30)}`) : expected;
  const body = ts.isBlock(fn.body) ? valueBlock(fn.body.statements, e2, retT, fn) : expr(fn.body, e2, retT);
  return { code: lets ? `(${lets}${body.code})` : body.code, type: body.type };
}

/**
 * An argument of `Math.<name>`: a number.  TypeScript accepts any subtype of `number`, also a
 * value of a type parameter `T extends int`, which is abstract in Lean (rejected like `x + 1`);
 * `expected` is the numeric type the argument is read at.
 */
function mathArg(name: string, a: ts.Expression, env: Env, expected?: VType): Val {
  const v = expr(a, env, operandExpected(a, env, expected));
  const tv = tvarPart(v.type);
  if (tv) fail(a, abstractMsg(tv, `Math.${name} on`));
  if (!isNumeric(v.type)) fail(a, `Math.${name} on ${showType(v.type)}: only numbers (int or number) are supported`);
  return expected ? coerce(v, expected, a, env) : v;
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
    const v = mathArg(name, args[0], env);
    if (v.type.k === "int") return v;
    // numbers: opaque (`Math.trunc` is not Lean's `Float.round`, nor any rounding Lean computes)
    return { code: `(VReact.JS.Num.${name} ${paren(v.code)})`, type: T.num };
  }
  if ((name === "round" || name === "ceil") && args.length === 1) {
    const v = mathArg(name, args[0], env);
    if (v.type.k === "int") return v;
    // `Math.round` rounds half-way cases towards +∞ (Lean's `Float.round` away from zero, and
    // `floor(x + 0.5)` is wrong for 0.49999999999999994 and -0.5): opaque
    return { code: `(VReact.JS.Num.${name} ${paren(v.code)})`, type: T.num };
  }
  if ((name === "max" || name === "min") && args.length >= 2) {
    let vs = args.map((a) => mathArg(name, a, env, expected?.k === "num" ? T.num : undefined));
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
    const v = mathArg(name, args[0], env);
    return v.type.k === "int" ? { code: `(VReact.JS.abs ${paren(v.code)})`, type: T.int } : { code: `(VReact.JS.Num.abs ${paren(v.code)})`, type: T.num };
  }
  if (name === "sign" && args.length === 1) {
    const v = mathArg(name, args[0], env, T.int);
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
      noIndexParam(name, args[0]);
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
      noIndexParam(name, args[0]);
      const lam = lambda(args[0], env, [elem], T.bool, [elT]);
      if (lam.obligations) fail(args[0], "findIndex predicates cannot contain proof obligations");
      return { code: `(VReact.JS.findIndex ${X} ${lamCode(lam.typed, lam.body.code)})`, type: T.int };
    }
    case "includes": {
      arity(c, "includes", 1, 1, "a fromIndex is not supported: write xs.slice(k).includes(v)");
      if (nullishSearch(c, (c.expression as ts.PropertyAccessExpression).expression, elem, args[0], "includes", env)) {
        return { code: `(${X}.any Option.isNone)`, type: T.bool };
      }
      checkPrimitiveElems(c, (c.expression as ts.PropertyAccessExpression).expression, elem, "includes", env);
      const v = expr(args[0], env, elem);
      return { code: `(${X}.contains ${paren(v.code)})`, type: T.bool };
    }
    case "indexOf": {
      arity(c, "indexOf", 1, 1, "a fromIndex is not supported");
      if (nullishSearch(c, (c.expression as ts.PropertyAccessExpression).expression, elem, args[0], "indexOf", env)) {
        return { code: `(VReact.JS.findIndex ${X} Option.isNone)`, type: T.int };
      }
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
      noIndexParam(name, args[0], 2);
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
      noIndexParam(name, args[0]);
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
      checkValueType(c.typeArguments![0], t, env.m.reg, "the hole's type");
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
    if (isNullLit(e.right, env) || isNullLit(e.left, env)) {
      const target = isNullLit(e.right, env) ? e.left : e.right;
      const key = pathKey(env, target);
      if (!key) return null;
      if (env.narrow.get(key)?.kind !== "some") checkStrictNullTest(e, target, isNullLit(e.right, env) ? e.right : e.left, k, env);
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
      if (["rec", "arr", "union", "tuple", "map", "set"].includes(t.elem.k)) {
        return narrowBranch({ kind: "null", target: e, positive: false }, env, onTrue, onFalse);
      }
      fail(c, `truthiness of ${showType(t)} is ambiguous (0, "" and false are falsy): compare with null explicitly`);
    }
    // an object known to be non-null (narrowed) is truthy
    if (t && ["rec", "arr", "union", "tuple"].includes(t.k) && narrowedSome(env, e)) return onTrue(env);
    if (t && (t.k === "map" || t.k === "set")) fail(c, `a ${t.k === "map" ? "Map" : "Set"} is always truthy, even when it is empty: test \`${nodeText(e, 30)}.size > 0\``);
  }
  const v = boolOperand(e, env);
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
      if (l.type.k === "tvar") fail(e, abstractMsg(l.type, "an ordering comparison (<, <=, >, >=) on"));
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
    // `m.has(k)` / `s.has(x)`: a membership
    if (ts.isPropertyAccessExpression(e.expression) && e.expression.name.text === "has" && !e.expression.questionDotToken) {
      let rt: VType | null = null;
      try {
        rt = typeOf(e.expression.expression, env);
      } catch (err) {
        if (!(err instanceof VtsError)) throw err;
      }
      if (rt?.k === "map" || rt?.k === "set") {
        arity(e, "has", 1, 1);
        const c = expr(e.expression.expression, env);
        const k = expr(args[0], env, rt.k === "map" ? rt.key : rt.elem);
        return `(${paren(k.code)} ∈ ${rt.k === "map" ? `(VReact.JS.JSMap.keys ${paren(c.code)})` : `(VReact.JS.JSSet.elems ${paren(c.code)})`})`;
      }
    }
    if (ts.isPropertyAccessExpression(e.expression) && ["every", "some", "includes"].includes(e.expression.name.text)) {
      const xs = expr(e.expression.expression, env);
      if (xs.type.k === "arr") {
        const mname = e.expression.name.text;
        if (mname === "includes") {
          arity(e, "includes", 1, 1, "a fromIndex is not supported: write xs.slice(k).includes(v)");
          if (nullishSearch(e, e.expression.expression, xs.type.elem, args[0], "includes", env)) return `(none ∈ ${paren(xs.code)})`;
          checkPrimitiveElems(e, e.expression.expression, xs.type.elem, "includes", env);
          return `(${expr(args[0], env, xs.type.elem).code} ∈ ${paren(xs.code)})`;
        }
        arity(e, mname, 1, 1, "a thisArg argument is not supported");
        const fn = args[0];
        noIndexParam(mname, fn);
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
  const v = boolOperand(e, env);
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
  /** an effect body: `return cleanup` (the cleanup's evaluation, then the outcome) */
  onCleanup?: (e: ts.Expression, env: Env) => string;
  /** an effect body: statements it translates itself (timer registrations), or null */
  onStmt?: (s: ts.Statement, env: Env, rest: (e: Env) => string) => string | null;
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
  const own = bc.onStmt?.(s, env, rest);
  if (own != null) return own;
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
      if (s.expression && bc.onCleanup) return bc.onCleanup(s.expression, env);
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
    checkPlainParams(init.parameters, `the local function ${d.name.text}`);
    return next(bind(env, symbolOf(env, d.name)!, { k: "closure", fn: init, env }));
  }
  // a data value (not a JSX element, nor a function: above, and useCallback below)
  const isJsxInit = ts.isJsxElement(init) || ts.isJsxSelfClosingElement(init) || ts.isJsxFragment(init);
  const isCallback = ts.isCallExpression(init) && hookName(env, init.expression) === "useCallback";
  if (declT && !isJsxInit && !isCallback) checkValueType(d.type!, declT, env.m.reg, `\`${d.name.getText()}\``);
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
    checkPlainParams(fn.parameters, `the local function ${d.name.text}`);
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
  if (ts.isArrayBindingPattern(d.name)) {
    // `const [k, v] = pair` on a tuple
    const v = expr(init, env, declT);
    const r = bindParam(d.name, v.type, env);
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

/** The generic top-level function whose body contains `node` (also inside a nested arrow), if any. */
function genericFunctionOf(node: ts.Node): ts.FunctionDeclaration | undefined {
  let n: ts.Node = node;
  while (n.parent && !ts.isSourceFile(n.parent)) n = n.parent;
  return ts.isFunctionDeclaration(n) && n.name && n.typeParameters?.length ? n : undefined;
}

/**
 * `assume(c)` is `have h : c := (by vreact_assume)`, and Lean keeps that proof as a theorem of
 * its own about the enclosing declaration's parameters (an auxiliary `f._proof_N`, which user
 * proofs can name): `∀ args, requires → path → c`, what the program's reviewer vouches for. In
 * a generic function that theorem is also `∀ {T : Type}` with the constraint's binders — every
 * Lean type, also ones with values JS never passes (`T extends boolean` at `Int`, where "two of
 * three values are equal" is false), so a fact true at every instantiation TypeScript allows
 * becomes a contradictory one (as for @trusted generics, `TRUSTED_GENERIC_MSG`). Rejected.
 */
const ASSUME_GENERIC_MSG = (name: string, tps: string[]) =>
  `assume(…) is not supported in a generic function (${name}<${tps.join(", ")}>): Lean keeps an assumed fact as a theorem about the function's parameters, and in a generic function for every type ${tps.join(", ")} (with the constraint's binders) — also for types with values JS never passes, where a fact true at every instantiation TypeScript allows can be false and contradictory; state the fact as requires(…) (each caller proves it, or assumes it, at its own types) or prove it with assert(…)`;

/**
 * Likewise where Lean checks a body for more values than JS gives it (`Env.generalized`): a
 * `for…of` body is a fold step over any accumulator and element (no membership), an
 * array-method callback a function of any element, a functional update one of any state, so
 * the theorem would be `∀ acc x, c` where JS only reaches the loop's own values
 * (`assume(s >= 0)` on a sum of non-negatives would be `∀ s, s ≥ 0`). Rejected.
 */
const ASSUME_GENERALIZED_MSG = (where: string) =>
  `assume(…) is not supported in ${where}; Lean keeps an assumed fact as a theorem about the values in scope, so it would be assumed for all of them — a stronger statement than the program's, possibly false; prove it with assert(…), or state what you need where the values come from (e.g. requires(…) of a helper function that takes them as parameters)`;

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
  // console.*(…), localStorage.setItem(…), document.title = …: external, no effect on component
  // state (of the globals: a local Map or a parameter named `console` / `document` is not one);
  // JS evaluates their arguments (which may throw, or call a function outside its
  // precondition), so the arguments are translated with their obligations (`evalArgs`)
  const ext = externalWriteArgs(e, env);
  if (ext) return evalArgs(ext, env, rest);
  // assignments
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (k === ts.SyntaxKind.EqualsToken) {
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
      const one = old.type.k === "num" ? `(VReact.JS.Num.ofInt ${leanInt(1)})` : leanInt(1);
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
        const ob = m.ob(e, "assert", `assertion ${exprText(e.arguments[0])}`);
        return `(have ${h} : ${p} := ${ob};\n${withFact(h, env, bc, rest)})`;
      }
      case "assume": {
        const gen = genericFunctionOf(e);
        if (gen) fail(e, ASSUME_GENERIC_MSG(gen.name!.text, gen.typeParameters!.map((t) => t.name.text)));
        if (env.generalized) fail(e, ASSUME_GENERALIZED_MSG(env.generalized));
        const p = prop(e.arguments[0], env);
        const h = m.fresh("hassume");
        // (`VReact.assumed` under the hypotheses in scope: the auxiliary theorem Lean makes of
        // this proof is the fact under the precondition and the path to it, VReact/Assumed.lean)
        return `(have ${h} : ${p} := (by vreact_assume);\n${withFact(h, env, bc, rest)})`;
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
  // e.preventDefault(), e.stopPropagation(): no effect on component state (console.*,
  // localStorage.setItem and document.title = … are taken above, `externalWriteArgs`)
  if (ts.isPropertyAccessExpression(callee)) {
    if (["preventDefault", "stopPropagation"].includes(callee.name.text) && ts.isIdentifier(callee.expression)) {
      const s = symbolOf(env, callee.expression);
      const b = s ? env.vars.get(s) : undefined;
      if (b?.k === "event") {
        checkEventUse(callee.expression, b, env);
        if (e.arguments.length) fail(e, `${callee.name.text}() takes no arguments`);
        return rest(env);
      }
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
      checkPlainParams(fn.parameters, `the local function ${callee.text}`);
      if (fn.parameters.length !== e.arguments.length) fail(e, `${callee.text} takes ${fn.parameters.length} argument(s), not ${e.arguments.length}`);
      let e2: Env = { ...b.env, handler: env.handler, scope: env.scope, curState: undefined, generalized: env.generalized ?? b.env.generalized };
      let lets = "";
      fn.parameters.forEach((p, i) => {
        if (!p.type) fail(p, "helper parameters need type annotations");
        const t = helperValueType(p.type, env, "Arg", `parameter \`${p.name.getText()}\` of ${callee.text}`);
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
      // (a `return` in the helper ends the helper: its value is not an effect's cleanup)
      const inner: BlockCtx = { ...bc, onCleanup: undefined, onStmt: undefined, onDone: (e3) => rest({ ...env, handler: e3.handler, scope: e3.scope }) };
      return `(${lets}${block(stmts, 0, e2, inner, (e3) => rest({ ...env, handler: e3.handler, scope: e3.scope }))})`;
    }
  }
  // `n.set(k, v)` / `n.add(x)` / `n.delete(k)` / `n.clear()` on a fresh local Map / Set
  if (ts.isPropertyAccessExpression(callee) && (MUTATORS.has(callee.name.text) || callee.name.text === "forEach")) {
    const kind = collectionKind(m.checker.getNonNullableType(m.checker.getTypeAtLocation(callee.expression)), m.prog.typeEnv);
    if (kind && callee.name.text === "forEach") fail(e, `${kind === "map" ? "Map" : "Set"}.forEach is not supported: write for (const ${kind === "map" ? "[k, v]" : "x"} of ${recvText(callee.expression, 30)}) { … }`);
    if (kind) return mutateLocal(e, callee, kind, env, rest);
  }
  if (ts.isPropertyAccessExpression(callee) && (ARRAY_MUTATORS.has(callee.name.text) || MUTATORS.has(callee.name.text))) {
    fail(e, `${callee.name.text} mutates the array/object; VTS data is immutable (use spread, filter, toSorted, toReversed, with)`);
  }
  if (ts.isCallExpression(e) && hookName(env, callee)) fail(e, "hooks must be called at the top level of a component, unconditionally (Rules of Hooks)");
  fail(e, `this call has no modelled effect: ${nodeText(e)}`);
}

// (`console`, `localStorage`, `document`, `JSON` and the timer functions are recognised as the
// browser's by their declaration: `isGlobal`)

/** `console.*(…)` / `localStorage.setItem(…)`: an external write, with no modelled effect. */
export function externalWrite(c: ts.CallExpression, env: Env): boolean {
  const callee = c.expression;
  if (!ts.isPropertyAccessExpression(callee)) return false;
  const obj = stripParens(callee.expression);
  return isGlobal(env, obj, "console") || (callee.name.text === "setItem" && isGlobal(env, obj, "localStorage"));
}

/** `document.title` (as an assignment target). */
export function isDocumentTitle(x0: ts.Expression, env: Env): boolean {
  const x = stripParens(x0);
  return ts.isPropertyAccessExpression(x) && x.name.text === "title" && isGlobal(env, stripParens(x.expression), "document");
}

/**
 * Evaluate the arguments of an external write, then `rest`: the values are not used, but JS
 * computes them, so they are translated (as unused `let`s) with their obligations — an index
 * `xs[9].name` or `x!.f` that would throw, a `%`/`idiv` divisor, the precondition of a called
 * function.  `null` / `undefined` need no evaluation.
 */
export function evalArgs(args: readonly ts.Expression[], env: Env, rest: (e: Env) => string): string {
  let lets = "";
  for (const a0 of args) {
    if (ts.isSpreadElement(a0)) fail(a0, "spread arguments are not supported here: pass the values one by one");
    let a = stripParens(a0);
    // JSON.stringify(v) (also (v, null, indent)) of a VTS value cannot throw (no cycles, BigInts
    // or toJSON methods; NaN becomes null): evaluating it is evaluating v
    const json = jsonStringifyArg(a, env);
    if (json) a = json;
    if (isNullLit(a, env)) continue;
    if (ts.isStringLiteralLike(a) || ts.isNumericLiteral(a) || a.kind === ts.SyntaxKind.TrueKeyword || a.kind === ts.SyntaxKind.FalseKeyword) continue;
    const v = expr(a, env);
    lets += `let _${letType(v.type)} := ${v.code};\n`;
  }
  return lets ? `(${lets}${rest(env)})` : rest(env);
}

/** `JSON.stringify(v)` / `JSON.stringify(v, null, indent)` (indent a literal): `v`. */
function jsonStringifyArg(a: ts.Expression, env: Env): ts.Expression | null {
  if (!ts.isCallExpression(a) || !ts.isPropertyAccessExpression(a.expression) || a.expression.name.text !== "stringify" || !isGlobal(env, a.expression.expression, "JSON")) return null;
  const [v, replacer, indent] = a.arguments;
  if (!v || ts.isSpreadElement(v) || a.arguments.length > 3) fail(a, "JSON.stringify(value) or JSON.stringify(value, null, indent)");
  if (replacer && replacer.kind !== ts.SyntaxKind.NullKeyword) fail(replacer, "a JSON.stringify replacer is not supported (pass null)");
  if (indent && !ts.isNumericLiteral(indent) && !ts.isStringLiteral(indent)) fail(indent, "the indent of JSON.stringify must be a literal");
  return v;
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
      const e2: Env = { ...r.env, curState: tau, generalized: "a functional update: Lean checks it for every value of its parameter (any state), not only the states React passes" };
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
    const r = sv.reducer!;
    const a = expr(c.arguments[0], env, sv.actionType);
    m.deps.add(r.qname);
    // A reducer's requires is about the action alone (component.ts, actionOnlyPre): proved here,
    // where the action is built from the snapshot, and it holds for whichever state τ React applies it to.
    const ob = r.hasPre ? " " + m.ob(c, "precondition", `precondition of ${r.name}(…, ${argText(c.arguments[0], 100)})`) : "";
    const upd = `(fun τ => { τ with ${leanField(sv.field)} := ${r.qname} τ.${leanField(sv.field)} ${paren(a.code)}${ob} })`;
    return rest({ ...env, handler: { ...h, updates: [...h.updates, upd] } });
  }
  // callback
  if (h.kind === "robust") fail(c, "parent callbacks cannot be invoked from effects, timers, continuous/default-priority events or onFocus/onBlur/onInvalid (robust handlers: they may run with a stale snapshot, or inside another event's batch)");
  if (h.emit) fail(c, "a handler may invoke at most one parent callback per execution path (otherwise the parent's updates would not be checked together)");
  const cb = comp.info.callbacks.find((x) => x.name === t.name)!;
  if (c.arguments.length !== cb.params.length) fail(c, `${cb.name} expects ${cb.params.length} arguments`);
  const as = c.arguments.map((a, i) => paren(expr(a, env, cb.params[i].type).code));
  const ob = m.ob(c, "callback-contract", `callback contract of ${cb.name}(${c.arguments.map((a) => argText(a)).join(", ")})${calledAs(c.expression, cb.name)}`);
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
  // an array, a Map (its entries), a Set, or an iterator (`m.keys()`, …): the list it visits
  const xs = iterated(s.expression, env).v;
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
    // a mutation statement `n.set(…)` of a fresh local Map / Set rebinds it (see mutateLocal)
    const mr = mutationReceiver(n);
    if (mr) {
      const sym = symbolOf(env, mr);
      const b = sym ? env.vars.get(sym) : undefined;
      if (sym && b?.k === "val" && (b.type.k === "map" || b.type.k === "set") && !assigned.includes(sym)) assigned.push(sym);
    }
    if (ts.isReturnStatement(n) || ts.isContinueStatement(n) || (ts.isBreakStatement(n) && (!!n.label || !sw))) fail(n, "return/break/continue inside for…of are not supported (a `break` may only end a switch case); use array methods (find, some, …)");
    if (ts.isCallExpression(n) && updateTarget(n.expression, env)) fail(n, "state updates inside loops are not supported; compute the new value, then update once");
    const inner = ts.isSwitchStatement(n) ? true : ts.isIterationStatement(n, false) ? false : sw;
    ts.forEachChild(n, (c) => visit(c, inner));
  };
  visit(s.statement);
  if (assigned.length === 0) fail(s, "loop has no effect (it assigns no local variable)");
  // JS visits the entries a loop adds to the Map / Set it iterates (and skips deleted ones)
  const iterRoot = iteratedRoot(s.expression);
  const iterSym = iterRoot ? symbolOf(env, iterRoot) : undefined;
  if (iterRoot && iterSym && assigned.includes(iterSym)) {
    const ib = env.vars.get(iterSym);
    if (ib?.k === "val" && (ib.type.k === "map" || ib.type.k === "set")) fail(s, ITERATE_MUTATE_MSG(iterRoot.text));
  }
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
  e1 = { ...e1, generalized: "a for…of loop body: Lean checks it for every value of the element and of the variables the loop assigns (as its obligations), not only those the loop reaches" };
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
 * Translate a function used as an event handler into `fun ev => outcome`.  `argTypes`: the
 * VTS types of the arguments of a callback, or the site of a DOM handler (its one parameter is
 * the event).  `paramTs`: the TypeScript types of the arguments (by default, those the context
 * of `fnExpr` gives them, e.g. the child's callback prop type for a JSX attribute), against
 * which annotations are checked.
 */
export function handlerFn(fnExpr: ts.Expression, env: Env, kind: "discrete" | "robust", argTypes: Param[] | DomSite, hyps?: string, paramTs?: ts.Type[] | null): { code: string; params: string[] } {
  const m = env.m;
  const comp = env.comp!;
  fnExpr = stripParens(fnExpr);
  if (paramTs === undefined) paramTs = !Array.isArray(argTypes) ? null : contextualParamTsTypes(fnExpr, env);
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
  if (!Array.isArray(argTypes)) {
    if (fnExpr.parameters.length > 1) fail(fnExpr, "DOM event handlers take at most one parameter (the event)");
    const p = fnExpr.parameters[0];
    if (p) {
      // React calls the handler with the event as its one argument: only a plain parameter is it
      // (`(...e) => e.key` reads the key of the array [event]: undefined)
      checkNotThisParam(p);
      const pname = p.name.getText();
      if (p.dotDotDotToken) fail(p, `a rest parameter \`...${pname}\` is the array of the handler's arguments ([event]), not the event (\`${pname}.key\` is undefined in JS): write (${pname}) => …`);
      if (p.initializer) fail(p.initializer, `a default value for the event parameter \`${pname}\` is not supported (React always passes the event): write (${pname}) => …`);
      if (p.questionToken) fail(p, `the event parameter \`${pname}?\` is not optional (React always passes the event): write (${pname}) => …`);
      if (!ts.isIdentifier(p.name)) fail(p, "destructuring the event object is not supported");
      if (p.name.text === "this" || p.dotDotDotToken) fail(p, "an event handler's parameter is the event: a plain parameter `(e) => …` (not `this` or a rest parameter)");
      const r = freshLocal(e1, leanIdent(p.name.text));
      e1 = bind(r.env, symbolOf(env, p.name)!, { k: "event", leanVar: r.name, fn: fnExpr, site: argTypes });
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

/** `, through the local pick` when a callback prop is reached through a renamed destructured local (`{ onPick: pick }`). */
function calledAs(callee: ts.Node, name: string): string {
  return ts.isIdentifier(callee) && callee.text !== name ? `, through the local ${callee.text}` : "";
}

function forwardCallback(cb: { name: string; params: Param[] }, node: ts.Node, env: Env, kind: "discrete" | "robust", argTypes: Param[] | DomSite): { code: string; params: string[] } {
  const comp = env.comp!;
  if (kind === "robust") fail(node, "parent callbacks cannot be invoked from effects, timers, continuous/default-priority events or onFocus/onBlur/onInvalid (robust handlers)");
  const ps = !Array.isArray(argTypes) ? [] : argTypes;
  if (!Array.isArray(argTypes) && cb.params.length) fail(node, `${cb.name} needs arguments; wrap it: () => ${cb.name}(…)`);
  if (Array.isArray(argTypes) && ps.length !== cb.params.length) fail(node, `callback arity mismatch forwarding ${cb.name}`);
  let e1 = env;
  const names: string[] = [];
  for (const p of ps) {
    const r = freshLocal(e1, leanIdent(p.name));
    e1 = r.env;
    names.push(r.name);
  }
  const ob = env.m.ob(node, "callback-contract", `contract of forwarded callback ${cb.name}${calledAs(node, cb.name)}`);
  const emit = `(${comp.cbVar}.${leanField(cb.name)}${names.map((n) => " " + n).join("")} ${ob})`;
  return { code: `(VReact.Outcome.mk (S := ${comp.stateType}) (E := E) [] (some ${emit}))`, params: !Array.isArray(argTypes) ? ["_"] : names };
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
