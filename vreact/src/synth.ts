/**
 * vreact synth — fill `hole<T>()` placeholders against the function's contract.
 *
 *   1. Scope: parameters of the enclosing function, refined by the narrowing in
 *      effect at the hole (switch/if on a discriminant, null tests, early returns,
 *      else branches, `&&`/`||`, `?:`), read from the translator's own environment
 *      at the hole (the narrowing every translation of the hole agrees on).
 *   2. Enumerate well-typed VTS expressions of type T, smallest first, from a
 *      grammar of idiomatic immutable updates: field updates `{ ...s, f: e }`,
 *      append `[...xs, e]`, remove-by-key `xs.filter(x => x.k !== v)`,
 *      update-by-key `xs.map(x => x.k === v ? { ...x, f: e } : x)`, record and
 *      variant literals, ±1 arithmetic, comparisons, calls of total helpers;
 *      Maps and Sets only grow: `new Map(m).set(k, v)`, `new Set(s).add(x)` (no
 *      deletion), with `m.get(k)`, `m.has(k)`, `.size`.
 *   3. Test each candidate by *running the real transpiled JavaScript* on random
 *      inputs: the function's own `requires` filters inputs, its own `ensures`
 *      must hold on the result (counterexample-driven pruning). Inputs that reach
 *      another, still unfilled hole are skipped. The inputs come from a seeded
 *      generator (`--seed N`, default 1; one per hole), so a run is reproducible
 *      up to the time limits, which hold while a candidate runs (vm timeouts).
 *   4. Prove the survivors with Lean, in order. A candidate is reported "proved"
 *      only when Lean elaborated the function and all its postcondition theorems,
 *      no obligation of the function failed, and their axioms contain no sorry.
 *      The holes of one function are filled together (the contract is only
 *      checked once the function is complete): a depth-first search over
 *      tentative fills, where the search of a hole that no execution reaching it
 *      shares with an earlier hole (another `case`, the other branch, after an
 *      early return) runs once and is reused whatever the earlier fills are, and
 *      a hole without survivors backjumps over the holes it does not depend on.
 *
 * Holes are filled in code only: a hole inside a contract (`requires`, `ensures`,
 * `assert`, …) is the specification the others are filled against, never filled.
 * The source file is never modified while searching: candidates are checked
 * from memory (`Config.overrides`). With `--write`, the proved fills are written
 * once at the end: exactly the text Lean checked last.
 */
import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { createRequire } from "node:module";
import { pathToFileURL } from "node:url";
import { loadConfig } from "./cli.ts";
import { translate, overrideHost, moduleNs, isComponentDecl, type Config, type TranslateResult } from "./module.ts";
import { runLake, findMarkers, judge, type Verdict } from "./lean.ts";
import { Program, ModCtx, refSymbol, type HoleEnv } from "./ctx.ts";
import { type VType, type Field, T, typeOfNode, typeOfDecl, showType, sharedFields, registerTypeParams, type TParam, type TypeRegistry, sameType, isEqType, substType, mentionsTVar, collectionTypeArgs } from "./types.ts";
import { specFn, narrowingAt, remainingAt } from "./translate.ts";
import { baseEnv } from "./component.ts";
import { VtsError, capitalize } from "./util.ts";

interface Atom {
  code: string;
  type: VType;
  size: number;
}

interface Hole {
  /** position among the holes of the file (source order) */
  index: number;
  node: ts.CallExpression;
  /** [start, end) of `hole<T>()` in the (BOM-less) source text */
  span: [number, number];
  type: VType;
  fn: ts.FunctionDeclaration;
  scope: Atom[];
  /** whether a non-atomic candidate needs parentheses at this position */
  parens: boolean;
}

/** One function with holes: its holes are filled (and proved) together. */
interface Task {
  fn: ts.FunctionDeclaration;
  name: string;
  holes: Hole[];
  /** number of `ensures` of the function (each one is a postcondition theorem) */
  ensures: number;
  /** holes inside the function's contract (`requires(hole<boolean>())`): never filled, the function is not searched */
  contractHoles: { where: string; call: string; type: string }[];
}

type Edit = { at: [number, number]; text: string };

const key = (t: VType) => JSON.stringify(t);
const MAX_TERMS = 3000;
const MAX_CANDIDATES = 30000;
const TIME_LIMIT_MS = 60000;
/** Lean checks per hole before giving up on further survivors (a function with n holes gets n × this in all) */
const MAX_LEAN_CHECKS = 5;
/** Lean checks of the last hole of a function with several holes, per fill of the earlier ones */
const MAX_LEAN_CHECKS_JOINT = 2;
/** survivors of a non-final hole explored (each one with a search for the next hole) */
const MAX_TENTATIVE = 3;
/** candidates sent to Lean untested when no generated input exercises the hole */
const MAX_UNTESTED = 3;
/** after this many candidates in a row that no input could test, the hole counts as one no input can test */
const MAX_UNTESTABLE_RUN = 50;
/** candidates whose tests were cut off (after passing some) held back for the ones whose tests finish */
const MAX_CUT_HELD = 3;
const STD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);
/**
 * The calls of vreact/spec whose argument is a contract, not code: a hole inside one is a
 * placeholder of the specification synth fills holes against (filling it against that same
 * contract is circular: `requires(false)` makes any body "proved"), so it is never filled.
 */
const CONTRACT_FNS = new Set(["requires", "ensures", "decreases", "invariant", "callbackRequires", "assert", "assume"]);
const SPEC_RE = /^vreact\/spec$/;


/* ───────────────────────── text edits ───────────────────────── */

function applyEdits(src: string, edits: Edit[]): string {
  let out = src;
  for (const e of [...edits].sort((a, b) => b.at[0] - a.at[0])) out = out.slice(0, e.at[0]) + e.text + out.slice(e.at[1]);
  return out;
}

/** Contexts in which an arbitrary expression can replace the hole without parentheses. */
function needsParens(hole: ts.CallExpression): boolean {
  const p = hole.parent;
  if (ts.isReturnStatement(p) || ts.isParenthesizedExpression(p) || ts.isTemplateSpan(p) || ts.isJsxExpression(p)) return false;
  if (ts.isVariableDeclaration(p) && p.initializer === hole) return false;
  if (ts.isPropertyAssignment(p) && p.initializer === hole) return false;
  if ((ts.isCallExpression(p) || ts.isNewExpression(p)) && p.arguments?.includes(hole)) return false;
  if (ts.isArrayLiteralExpression(p)) return false;
  if (ts.isConditionalExpression(p) && p.condition !== hole) return false;
  // the whole condition of an `if`, a loop or a `switch`
  if ((ts.isIfStatement(p) || ts.isWhileStatement(p) || ts.isDoStatement(p) || ts.isSwitchStatement(p)) && p.expression === hole) return false;
  return true;
}

/** Candidates that bind tighter than any operator (no parentheses needed anywhere but statement starts). */
function isAtomic(code: string): boolean {
  const sf = ts.createSourceFile("c.ts", `(${code});`, ts.ScriptTarget.ES2022, true);
  const st = sf.statements[0];
  if (sf.statements.length !== 1 || !ts.isExpressionStatement(st) || !ts.isParenthesizedExpression(st.expression)) return false;
  const e = st.expression.expression;
  if (e.getText(sf) !== code) return false;
  const K = ts.SyntaxKind;
  return [K.Identifier, K.PropertyAccessExpression, K.ElementAccessExpression, K.CallExpression, K.NewExpression, K.NumericLiteral, K.StringLiteral, K.NoSubstitutionTemplateLiteral, K.ArrayLiteralExpression, K.TrueKeyword, K.FalseKeyword, K.NullKeyword, K.ParenthesizedExpression].includes(e.kind);
}

/** The text that replaces a hole: the candidate, parenthesized when precedence requires it. */
function fillText(h: Hole, cand: string): string {
  return h.parens && !isAtomic(cand) ? `(${cand})` : cand;
}

/** A single-file program (nothing resolved, no lib) whose checker binds the file's own names. */
function fileChecker(fileName: string, text: string): { sf: ts.SourceFile; checker: ts.TypeChecker } {
  const sf = ts.createSourceFile(fileName, text, ts.ScriptTarget.ES2022, true, fileName.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
  const host: ts.CompilerHost = {
    getSourceFile: (f) => (f === fileName ? sf : undefined),
    getDefaultLibFileName: () => "lib.d.ts",
    writeFile: () => {},
    getCurrentDirectory: () => path.dirname(fileName),
    getCanonicalFileName: (f) => f,
    useCaseSensitiveFileNames: () => true,
    getNewLine: () => "\n",
    fileExists: (f) => f === fileName,
    readFile: (f) => (f === fileName ? text : undefined),
  };
  const program = ts.createProgram({ rootNames: [fileName], options: { noResolve: true, noLib: true, types: [], jsx: ts.JsxEmit.Preserve }, host });
  return { sf, checker: program.getTypeChecker() };
}

/** An identifier that names a property (`x.f`, `{ f: e }`, `{ f: T }`, `{ f: y } = e`), never a variable. */
function isPropertyName(n: ts.Identifier): boolean {
  const p = n.parent;
  if (ts.isPropertyAccessExpression(p)) return p.name === n;
  if (ts.isQualifiedName(p)) return p.right === n;
  if (ts.isPropertyAssignment(p) || ts.isPropertySignature(p) || ts.isPropertyDeclaration(p) || ts.isMethodDeclaration(p) || ts.isMethodSignature(p) || ts.isGetAccessor(p) || ts.isSetAccessor(p) || ts.isEnumMember(p)) return p.name === n;
  if (ts.isBindingElement(p)) return p.propertyName === n;
  if (ts.isJsxAttribute(p)) return p.name === n;
  return false;
}

/**
 * The bindings a text declares that a fill can leave without a use: the names its imports bind
 * (`hole` from vreact/spec, a type imported for a hole's type argument) and its own type aliases
 * and interfaces that are not exported, each with whether the text uses it outside its own
 * declaration (by symbol: not a field or property spelled like it, nor a local that shadows it).
 */
interface Binding {
  key: string;
  name: ts.Identifier;
  decl: ts.Statement;
  used: boolean;
}

function bindingsOf(text: string, fileName: string): { sf: ts.SourceFile; bindings: Binding[] } {
  const { sf, checker } = fileChecker(fileName, text);
  const found: { key: string; name: ts.Identifier; decl: ts.Statement }[] = [];
  for (const st of sf.statements) {
    if (ts.isImportDeclaration(st) && ts.isStringLiteral(st.moduleSpecifier) && st.importClause) {
      const from = st.moduleSpecifier.text;
      const c = st.importClause;
      if (c.name) found.push({ key: `import\u0000${from}\u0000${c.name.text}`, name: c.name, decl: st });
      const nb = c.namedBindings;
      if (nb && ts.isNamespaceImport(nb)) found.push({ key: `import\u0000${from}\u0000${nb.name.text}`, name: nb.name, decl: st });
      if (nb && ts.isNamedImports(nb)) for (const e of nb.elements) found.push({ key: `import\u0000${from}\u0000${e.name.text}`, name: e.name, decl: st });
    } else if ((ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) && !st.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword || m.kind === ts.SyntaxKind.DefaultKeyword || m.kind === ts.SyntaxKind.DeclareKeyword)) {
      found.push({ key: `type\u0000${st.name.text}`, name: st.name, decl: st });
    }
  }
  const bindings = found.map((b) => {
    const sym = checker.getSymbolAtLocation(b.name);
    let used = false;
    const visit = (n: ts.Node) => {
      if (used || n === b.decl) return;
      if (ts.isIdentifier(n) && n.text === b.name.text && !isPropertyName(n)) {
        const p = n.parent;
        // (an export specifier, or no symbol at all: kept, to be safe)
        const s = ts.isExportSpecifier(p) ? undefined : ts.isShorthandPropertyAssignment(p) && p.name === n ? checker.getShorthandAssignmentValueSymbol(p) : checker.getSymbolAtLocation(n);
        if (!sym || !s || s === sym) used = true;
      }
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(sf, visit);
    return { ...b, used };
  });
  return { sf, bindings };
}

/** Delete statement `st` with its JSDoc and its line break. */
function statementCut(text: string, sf: ts.SourceFile, st: ts.Statement): Edit {
  let end = st.getEnd();
  if (text[end] === "\r") end++;
  if (text[end] === "\n") end++;
  return { at: [st.getStart(sf, true), end], text: "" };
}

/**
 * After the fills (noUnusedLocals): drop each binding the original text used and the filled text
 * no longer uses — the `hole` import, and an import or a type of the file's own (not exported)
 * whose only uses were in replaced `hole<T>()` calls — until none is left. A binding the user left
 * unused stays. The uses a fill removes are all type arguments of `hole`, so the module's
 * JavaScript stays the same (TypeScript emits no import that only types use).
 */
function dropUnusedAfterFill(text: string, fileName: string, usedInBase: (key: string) => boolean): string {
  for (let round = 0; round < 20; round++) {
    const { sf, bindings } = bindingsOf(text, fileName);
    const gone = new Set(bindings.filter((b) => !b.used && usedInBase(b.key)).map((b) => b.name));
    if (!gone.size) return text;
    const edits: Edit[] = [];
    for (const st of sf.statements) {
      if (ts.isImportDeclaration(st) && st.importClause) {
        const c = st.importClause;
        const nb = c.namedBindings;
        const names = [c.name, ...(nb && ts.isNamespaceImport(nb) ? [nb.name] : []), ...(nb && ts.isNamedImports(nb) ? nb.elements.map((e) => e.name) : [])].filter((x): x is ts.Identifier => !!x);
        if (!names.some((x) => gone.has(x))) continue;
        const keepDefault = !!c.name && !gone.has(c.name);
        const keptNamed = nb && ts.isNamedImports(nb) ? nb.elements.filter((e) => !gone.has(e.name)) : [];
        const keepNs = !!nb && ts.isNamespaceImport(nb) && !gone.has(nb.name);
        if (!keepDefault && !keptNamed.length && !keepNs) {
          edits.push(statementCut(text, sf, st)); // the whole import goes
          continue;
        }
        if (nb && ts.isNamedImports(nb) && keptNamed.length < nb.elements.length) {
          if (keptNamed.length) edits.push({ at: [nb.getStart(sf), nb.getEnd()], text: `{ ${keptNamed.map((e) => e.getText(sf)).join(", ")} }` });
          else edits.push({ at: [c.name!.getEnd(), nb.getEnd()], text: "" }); // `X, { a }` → `X`
        }
        if (nb && ts.isNamespaceImport(nb) && !keepNs) edits.push({ at: [c.name!.getEnd(), nb.getEnd()], text: "" }); // `X, * as N` → `X`
        if (c.name && !keepDefault) edits.push({ at: [c.name.getStart(sf), nb!.getStart(sf)], text: "" }); // `X, { a }` → `{ a }`
      } else if ((ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) && gone.has(st.name)) {
        edits.push(statementCut(text, sf, st));
      }
    }
    text = applyEdits(text, edits);
  }
  return text;
}

/* ───────────────────────── optional types: null vs undefined ───────────────────────── */

type Absent = "null" | "undefined" | "both";
/** synth-local annotation of `opt` types: which absent value(s) TypeScript allows */
type OptT = Extract<VType, { k: "opt" }> & { absent?: Absent };

function absentOf(tt: ts.Type, optional: boolean): Absent {
  const parts = tt.isUnion() ? tt.types : [tt];
  const n = parts.some((p) => p.flags & ts.TypeFlags.Null);
  const u = optional || parts.some((p) => p.flags & ts.TypeFlags.Undefined);
  return n && u ? "both" : u ? "undefined" : "null";
}

/** Record on each `opt` VType (in place, synth-local objects) the absent value TS allows there. */
function annotateOpt(t: VType, tt: ts.Type | undefined, checker: ts.TypeChecker, optional = false) {
  if (!tt) return;
  if (t.k === "opt") {
    (t as OptT).absent = absentOf(tt, optional);
    annotateOpt(t.elem, checker.getNonNullableType(tt), checker);
  } else if (t.k === "arr") {
    annotateOpt(t.elem, checker.getIndexTypeOfType(tt, ts.IndexKind.Number), checker);
  } else if (t.k === "map") {
    // (keys are never optional; a value may have optional parts)
    const args = collectionTypeArgs(tt, checker);
    if (args?.length === 2) annotateOpt(t.val, args[1], checker);
  } else if (t.k === "tuple" && checker.isTupleType(tt)) {
    const args = checker.getTypeArguments(tt as ts.TypeReference);
    t.elems.forEach((e, i) => annotateOpt(e, args[i], checker));
  }
}

function annotateRegistry(prog: Program, checker: ts.TypeChecker) {
  for (const nt of prog.reg.byName.values()) {
    const d = nt.decl;
    if (!d) continue;
    const at = ts.isTypeAliasDeclaration(d) || ts.isInterfaceDeclaration(d) ? d.name : d;
    let tt: ts.Type;
    try {
      tt = checker.getTypeAtLocation(at);
    } catch {
      continue;
    }
    const fieldsOn = (obj: ts.Type, fields: Field[]) => {
      for (const f of fields) {
        const sym = checker.getPropertyOfType(obj, f.name);
        if (!sym) continue;
        const decl = sym.valueDeclaration ?? sym.declarations?.[0];
        const ft = decl ? checker.getTypeOfSymbolAtLocation(sym, decl) : checker.getTypeOfSymbol(sym);
        annotateOpt(f.type, ft, checker, !!(sym.flags & ts.SymbolFlags.Optional));
      }
    };
    if (nt.def.k === "rec") fieldsOn(tt, nt.def.fields);
    else if (nt.def.k === "union") {
      const tag = nt.def.tag;
      const parts = checker.getNonNullableType(tt);
      const members = parts.isUnion() ? parts.types : [parts];
      for (const v of nt.def.variants) {
        const m = members.find((p) => {
          const s = checker.getPropertyOfType(p, tag);
          const st = s && checker.getTypeOfSymbol(s);
          return !!st && st.isStringLiteral() && st.value === v.lit;
        });
        if (m) fieldsOn(m, v.fields);
      }
    }
  }
}

/* ───────────────────────── scope at the hole ───────────────────────── */

/**
 * What is known at a hole about a parameter path (`s`, `s.inner`): the variants it can have (one
 * when it is narrowed to a variant; absent: any), and whether it is present (not null).
 */
type Narrow = Map<string, { variants?: string[]; some?: boolean }>;

/**
 * The narrowing at each hole of the program, by the hole's start offset in its file: read from
 * the translator's environments at the hole (`Config.holeEnvs`), so that synth types candidates
 * exactly as the translator will. A variant narrowing implies a present value (`s: Shape | null`
 * tested to be a "rect"). Where tests excluded variants but several are left, the translator
 * keeps one arm and splits it when the code there needs a variant (`Env.remaining`): the
 * variants left are what synth may assume. A hole translated several times (the code after an
 * `if` without `else` is translated in both branches) keeps only what holds in every
 * translation: the union of the variants, and presence when every translation has it.
 */
function narrowingAtHoles(holeEnvs: HoleEnv[]): Map<string, Narrow> {
  const all = new Map<string, Narrow[]>();
  for (const { node, env } of holeEnvs) {
    let fn: ts.Node | undefined = node;
    while (fn && !(ts.isFunctionDeclaration(fn) && ts.isSourceFile(fn.parent))) fn = fn.parent;
    if (!fn) continue;
    const roots: { sym: ts.Symbol; name: string }[] = [];
    for (const p of (fn as ts.FunctionDeclaration).parameters) {
      const sym = ts.isIdentifier(p.name) ? env.m.checker.getSymbolAtLocation(p.name) : undefined;
      if (sym) roots.push({ sym, name: (p.name as ts.Identifier).text });
    }
    const facts: Narrow = new Map();
    for (const [p, n] of narrowingAt(env, roots)) facts.set(p, n.kind === "variant" && n.variant ? { variants: [n.variant], some: true } : { some: true });
    for (const [p, vs] of remainingAt(env, roots)) {
      const f = facts.get(p);
      if (!f?.variants) facts.set(p, { ...f, variants: vs });
    }
    const sf = node.getSourceFile();
    const k = `${path.resolve(sf.fileName)}:${node.getStart(sf)}`;
    all.set(k, [...(all.get(k) ?? []), facts]);
  }
  const out = new Map<string, Narrow>();
  for (const [k, facts] of all) {
    const agreed: Narrow = new Map();
    for (const p of new Set(facts.flatMap((f) => [...f.keys()]))) {
      const some = facts.every((f) => f.get(p)?.some);
      const variants = facts.every((f) => f.get(p)?.variants) ? [...new Set(facts.flatMap((f) => f.get(p)!.variants!))] : undefined;
      if (some || variants) agreed.set(p, { ...(variants ? { variants } : {}), ...(some ? { some } : {}) });
    }
    out.set(k, agreed);
  }
  return out;
}

/** A field read as `o.f`: its name is an identifier name (a field such as "my-field" has no such read in VTS, which rejects `o["my-field"]`). */
const isIdentName = (f: string) => /^[\p{ID_Start}$_][\p{ID_Continue}$\u200C\u200D]*$/u.test(f);
/** The key of a field in an object literal: `f`, or `"my-field"`. */
const propKey = (f: string) => (isIdentName(f) ? f : JSON.stringify(f));

function holeScope(narrowed: Narrow, prog: Program, params: Map<string, VType>): Atom[] {
  const reg = prog.reg;
  // the fields of a value of type t (of a union: those its possible variants share)
  const fieldsOf = (t: VType, variants?: string[]): Field[] => {
    if (t.k === "rec") return reg.rec(t);
    if (t.k === "union") {
      const u = reg.union(t);
      return sharedFields(variants ? u.variants.filter((v) => variants.includes(v.lit)) : u.variants);
    }
    // a type parameter's constrained fields (`x.id` with `T extends { readonly id: int }`)
    if (t.k === "tvar") return t.fields ?? [];
    return [];
  };
  const scope: Atom[] = [];
  const narrowT = (p: string, t: VType) => (narrowed.get(p)?.some && t.k === "opt" ? t.elem : t);
  for (const [name, t0] of params) {
    const t = narrowT(name, t0);
    scope.push({ code: name, type: t, size: 1 });
    // one level of field access (two for records of records / narrowed variants)
    for (const f of fieldsOf(t, narrowed.get(name)?.variants)) {
      if (!isIdentName(f.name)) continue;
      const p = `${name}.${f.name}`;
      const ft = narrowT(p, f.type);
      scope.push({ code: p, type: ft, size: 1 });
      if (ft.k === "rec" || (ft.k === "union" && narrowed.get(p)?.variants)) {
        for (const g of fieldsOf(ft, narrowed.get(p)?.variants)) if (isIdentName(g.name)) scope.push({ code: `${p}.${g.name}`, type: narrowT(`${p}.${g.name}`, g.type), size: 2 });
      }
    }
  }
  return scope;
}

/* ───────────────────────── holes that share executions ───────────────────────── */

const isFunctionLike = (n: ts.Node) => ts.isArrowFunction(n) || ts.isFunctionExpression(n) || ts.isFunctionDeclaration(n) || ts.isMethodDeclaration(n);

/** The statements end the function (as the translator's `terminates`: return/throw, or an if/else whose branches both do). */
function terminates(stmts: readonly ts.Statement[]): boolean {
  const last = stmts[stmts.length - 1];
  if (!last) return false;
  if (ts.isReturnStatement(last) || ts.isThrowStatement(last)) return true;
  if (ts.isBlock(last)) return terminates(last.statements);
  if (ts.isIfStatement(last)) return !!last.elseStatement && terminates(blockOf(last.thenStatement)) && terminates(blockOf(last.elseStatement));
  return false;
}
const blockOf = (s: ts.Statement): readonly ts.Statement[] => (ts.isBlock(s) ? s.statements : [s]);

/**
 * Does every execution that evaluates `h` (inside statement `top`) leave the function before
 * `top` completes? Yes when `h` is evaluated in a `return`/`throw` of the function itself (not of
 * a nested arrow function), or in a statement whose remaining statements in its block end the
 * function. (VTS has no `break` other than the one ending a `case`, and no `continue`.)
 */
function exitsAfter(h: ts.Node, top: ts.Node): boolean {
  let exits = false;
  for (let n = h; n !== top && n.parent; n = n.parent) {
    const p = n.parent;
    if (isFunctionLike(p)) exits = false; // its returns end the nested function, not this one
    else if (ts.isReturnStatement(p) || ts.isThrowStatement(p)) exits = true;
    else if ((ts.isBlock(p) || ts.isCaseClause(p) || ts.isDefaultClause(p)) && terminates(p.statements.slice(p.statements.indexOf(n as ts.Statement)))) exits = true;
  }
  return exits;
}

/**
 * Can one call of `fn` evaluate both holes `a` and `b` (`a` first in the source)? Conservatively
 * yes, unless the holes are in different branches of an `if`/`?:`, in different cases of a
 * `switch` (VTS cases never fall through), or `a` is in a statement that leaves the function
 * once `a` is evaluated (an early return before `b`) — all outside any loop or nested function,
 * in a function that does not call itself. Exclusive holes are searched independently (the
 * inputs that reach one never evaluate the other); this only saves time: Lean checks all fills
 * of a function together whatever this says.
 */
function mayShareExecution(a: ts.Node, b: ts.Node, fn: ts.FunctionDeclaration, recursive: boolean): boolean {
  if (recursive) return true;
  const chain = (n: ts.Node) => {
    const xs: ts.Node[] = [];
    for (let x: ts.Node | undefined = n; x && x !== fn; x = x.parent) xs.push(x);
    return xs;
  };
  const pa = chain(a);
  const pb = chain(b);
  const inB = new Set(pb);
  const i = pa.findIndex((x) => inB.has(x));
  if (i <= 0) return true;
  const lca = pa[i];
  const ca = pa[i - 1];
  const cb = pb[pb.indexOf(lca) - 1];
  if (!cb) return true;
  // the common ancestor runs at most once per call
  if (pa.slice(i).some((x) => isFunctionLike(x) || ts.isIterationStatement(x, false))) return true;
  const apart = (x: ts.Node, y: ts.Node) => (ca === x && cb === y) || (ca === y && cb === x);
  if (ts.isIfStatement(lca)) return !(lca.elseStatement && apart(lca.thenStatement, lca.elseStatement));
  if (ts.isConditionalExpression(lca)) return !apart(lca.whenTrue, lca.whenFalse);
  if (ts.isCaseBlock(lca)) return !((ts.isCaseClause(ca) || ts.isDefaultClause(ca)) && (ts.isCaseClause(cb) || ts.isDefaultClause(cb)) && ca.statements.length > 0);
  if (ts.isBlock(lca) || ts.isCaseClause(lca) || ts.isDefaultClause(lca)) return !exitsAfter(a, ca);
  return true;
}

/** Does `fn` call itself (directly, through other functions, or from its contract)? */
function callsItself(fn: ts.FunctionDeclaration, checker: ts.TypeChecker, refs: Set<ts.FunctionDeclaration>): boolean {
  if (refs.has(fn)) return true;
  let found = false;
  const visit = (n: ts.Node) => {
    if (found) return;
    if (ts.isIdentifier(n) && n !== fn.name) {
      let s = refSymbol(checker, n);
      if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
      if (s?.declarations?.includes(fn)) found = true;
    }
    ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return found;
}

/* ───────────────────────── candidate texts ───────────────────────── */

/** A candidate up to whitespace and redundant parentheses: its syntax tree without the parenthesized-expression nodes. */
function canonical(code: string): string {
  const sf = ts.createSourceFile("c.ts", `(${code});`, ts.ScriptTarget.ES2022, false);
  const walk = (n: ts.Node): string => {
    if (ts.isParenthesizedExpression(n)) return walk(n.expression);
    const kids: string[] = [];
    n.forEachChild((c) => {
      kids.push(walk(c));
    });
    const op = ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n) ? `${n.operator}` : "";
    return kids.length ? `${n.kind}${op}(${kids.join(",")})` : `${n.kind}:${n.getText(sf)}`;
  };
  return walk(sf);
}

/* ───────────────────────── enumeration ───────────────────────── */

export interface Helper {
  name: string;
  params: VType[];
  ret: VType;
}

/** A generic helper of the module: offered at instantiations of its type parameters (`instantiateHelper`). */
interface GenericHelper extends Helper {
  tparams: readonly TParam[];
  /** the TypeScript types of the parameters and the result (their null/undefined kinds) */
  paramTs: ts.Type[];
  retTs: ts.Type;
}

/** at most this many instantiations of one generic helper per hole */
const MAX_INSTANTIATIONS = 6;

/**
 * The instantiations of a generic helper at the types `types` (the hole's), as monomorphic
 * helpers: each type parameter at a type the translator accepts for it (`checkInstantiation`):
 * never optional, void, a function or a React node; a type JS compares by value for an equality
 * constraint; a type with each constrained field at exactly its type for a field constraint
 * (not offered for constrained fields with null/undefined parts, whose nullish kinds must match).
 */
function instantiateHelper(gh: GenericHelper, types: readonly VType[], reg: TypeRegistry, checker: ts.TypeChecker): Helper[] {
  const fieldType = (t: VType, name: string): VType | null => {
    if (t.k === "rec") return reg.rec(t).find((f) => f.name === name)?.type ?? null;
    if (t.k === "union") return sharedFields(reg.union(t).variants).find((f) => f.name === name)?.type ?? null;
    if (t.k === "tvar") return t.fields?.find((f) => f.name === name)?.type ?? null;
    return null;
  };
  const hasOpt = (t: VType): boolean => t.k === "opt" || ((t.k === "arr") && hasOpt(t.elem)) || (t.k === "tuple" && t.elems.some(hasOpt));
  const fits = (t: VType, p: TParam): boolean => {
    if (t.k === "opt" || t.k === "void" || t.k === "unit" || t.k === "fn" || t.k === "node") return false;
    if (p.eq) return isEqType(t);
    if (p.fields) return p.fields.every((f) => !hasOpt(f.type) && ((ft) => !!ft && sameType(ft, f.type))(fieldType(t, f.name)));
    return true;
  };
  let σs: Map<number, VType>[] = [new Map()];
  for (const p of gh.tparams) {
    const next: Map<number, VType>[] = [];
    for (const σ of σs) for (const t of types) if (fits(t, p)) next.push(new Map([...σ, [p.id, t]]));
    σs = next.slice(0, MAX_INSTANTIATIONS);
  }
  return σs.map((σ) => {
    const h: Helper = { name: gh.name, params: gh.params.map((t) => substType(t, σ)), ret: substType(gh.ret, σ) };
    h.params.forEach((t, i) => annotateOpt(t, gh.paramTs[i], checker));
    annotateOpt(h.ret, gh.retTs, checker);
    return h;
  });
}

class Enumerator {
  helpers: Helper[] = [];
  prog: Program;
  bySize = new Map<string, Atom[][]>(); // type key → terms by size
  types = new Map<string, VType>();
  scope: Atom[];
  maxSize: number;
  lambdaDepth = 0;
  /** some sub-term table was truncated at MAX_TERMS (the search is incomplete) */
  capped = false;
  constructor(prog: Program, scope: Atom[], target: VType, maxSize: number) {
    this.prog = prog;
    this.scope = scope;
    this.maxSize = maxSize;
    this.register(target);
    for (const a of scope) this.register(a.type);
  }
  register(t: VType) {
    const k = key(t);
    if (this.types.has(k)) return;
    this.types.set(k, t);
    const reg = this.prog.reg;
    if (t.k === "rec") for (const f of reg.rec(t)) this.register(f.type);
    if (t.k === "union") for (const v of reg.union(t).variants) for (const f of v.fields) this.register(f.type);
    if (t.k === "arr" || t.k === "opt") this.register(t.elem);
    if (t.k === "arr") this.register(T.int);
    if (t.k === "tvar") for (const f of t.fields ?? []) this.register(f.type);
    // Map / Set: their keys, values and elements, `size` and `has`
    if (t.k === "map") {
      this.register(t.key);
      this.register(t.val);
    }
    if (t.k === "set") this.register(t.elem);
    if (t.k === "map" || t.k === "set") {
      this.register(T.int);
      this.register(T.bool);
    }
  }
  terms(t: VType, size: number): Atom[] {
    const k = key(t);
    let tab = this.bySize.get(k);
    if (!tab) {
      tab = [];
      this.bySize.set(k, tab);
    }
    if (tab[size] === undefined) {
      // bound the search space: keep the first MAX_TERMS terms of each type and size
      const built: Atom[] = [];
      for (const a of this.build(t, size)) {
        if (built.length === MAX_TERMS) {
          this.capped = true;
          break;
        }
        built.push(a);
      }
      tab[size] = built;
    }
    return tab[size];
  }
  /** all terms of type t with size ≤ s */
  upTo(t: VType, s: number): Atom[] {
    const out: Atom[] = [];
    for (let i = 1; i <= s; i++) out.push(...this.terms(t, i));
    return out;
  }
  literals(t: VType): string[] {
    switch (t.k) {
      case "int":
        return ["0", "1"];
      case "bool":
        return ["true", "false"];
      case "str":
        return ['""'];
      case "enum":
        return this.prog.reg.enumLits(t).map((l) => JSON.stringify(l));
      case "opt": {
        const a = (t as OptT).absent ?? "null";
        return a === "both" ? ["null", "undefined"] : [a];
      }
      case "arr":
        return ["[]"];
      // (typed by the hole's context: its expected type, which TypeScript infers the arguments from)
      case "map":
        return ["new Map()"];
      case "set":
        return ["new Set()"];
      default:
        return [];
    }
  }
  /**
   * The terms of type t and size `size`, lazily (in a fixed order): the search tests them as they
   * come, under its time limit, and a table keeps the first MAX_TERMS; nothing builds every
   * combination of a wide literal or call first (their number grows exponentially with the fields).
   */
  *build(t: VType, size: number): Generator<Atom> {
    const reg = this.prog.reg;
    const mk = (code: string): Atom => ({ code, type: t, size });
    const same = (a: VType) => key(a) === key(t);
    if (size === 1) {
      for (const a of this.scope) if (a.size === 1 && same(a.type)) yield mk(a.code);
      for (const l of this.literals(t)) yield mk(l);
      return;
    }
    if (size === 2) for (const a of this.scope) if (a.size === 2 && same(a.type)) yield mk(a.code);
    // calls of helper functions of the module: f(a1, …, an)
    for (const h of this.helpers) {
      if (!same(h.ret) || h.params.length === 0 || size - 1 < h.params.length) continue;
      for (const split of splits(size - 1, h.params.length)) {
        const lists = this.parts(h.params, split, 2000, (_i, code) => code);
        if (lists) for (const args of product(lists)) yield mk(`${h.name}(${args.join(", ")})`);
      }
    }
    switch (t.k) {
      case "int": {
        for (const a of this.terms(T.int, size - 1)) {
          yield mk(`${a.code} + 1`);
          yield mk(`${a.code} - 1`);
        }
        for (const [i, j] of splits(size - 1, 2)) for (const a of this.terms(T.int, i)) for (const b of this.terms(T.int, j)) if (a.code < b.code) yield mk(`${a.code} + ${b.code}`);
        for (const [tk, tt] of this.types) if (tt.k === "arr") for (const a of this.terms(tt, size - 1)) if (!a.code.includes("=>")) yield mk(`${a.code}.length`);
        for (const [, tt] of this.types) if (tt.k === "map" || tt.k === "set") for (const a of this.terms(tt, size - 1)) yield mk(`${wrap(a.code)}.size`);
        break;
      }
      case "bool": {
        for (const a of this.terms(T.bool, size - 1)) yield mk(`!${wrap(a.code)}`);
        for (const [i, j] of splits(size - 1, 2)) {
          // (values of a type parameter: only under an equality constraint)
          const eqTVars = [...this.types.values()].filter((x) => x.k === "tvar" && x.eq);
          for (const pt of [T.int, T.str, ...eqTVars]) {
            for (const a of this.terms(pt, i)) for (const b of this.terms(pt, j)) {
              if (a.code === b.code) continue;
              yield mk(`${wrap(a.code)} === ${wrap(b.code)}`);
              if (pt.k === "int") yield mk(`${wrap(a.code)} < ${wrap(b.code)}`);
            }
          }
          // m.has(k), s.has(x)
          for (const [, tt] of this.types) {
            if (tt.k !== "map" && tt.k !== "set") continue;
            for (const c of this.terms(tt, i)) for (const k of this.terms(tt.k === "map" ? tt.key : tt.elem, j)) yield mk(`${wrap(c.code)}.has(${k.code})`);
          }
        }
        break;
      }
      case "str": {
        for (const a of this.terms(T.str, size - 1)) if (!a.code.endsWith(".trim()")) yield mk(`${wrap(a.code)}.trim()`);
        break;
      }
      case "opt": {
        for (const a of this.terms(t.elem, size - 1)) yield mk(a.code);
        // m.get(k): undefined for a missing key
        if ((t as OptT).absent !== "null") {
          for (const [, tt] of this.types) {
            if (tt.k !== "map" || key(tt.val) !== key(t.elem)) continue;
            for (const [i, j] of splits(size - 1, 2)) for (const m of this.terms(tt, i)) for (const k of this.terms(tt.key, j)) yield mk(`${wrap(m.code)}.get(${k.code})`);
          }
        }
        break;
      }
      case "map": {
        // a pure update of a fresh copy: new Map(m).set(k, v)
        for (const [i, j, l] of splits(size - 1, 3)) {
          for (const m of this.terms(t, i)) {
            if (m.code.startsWith("new Map()")) continue;
            for (const k of this.terms(t.key, j)) for (const v of this.terms(t.val, l)) yield mk(`new Map(${m.code}).set(${k.code}, ${v.code})`);
          }
        }
        break;
      }
      case "set": {
        // new Set(s).add(x)
        for (const [i, j] of splits(size - 1, 2)) {
          for (const s of this.terms(t, i)) {
            if (s.code.startsWith("new Set()")) continue;
            for (const x of this.terms(t.elem, j)) yield mk(`new Set(${s.code}).add(${x.code})`);
          }
        }
        break;
      }
      case "rec": {
        const fields = reg.rec(t);
        // { ...v, f: e }
        for (const [i, j] of splits(size - 1, 2)) {
          for (const v of this.terms(t, i)) {
            if (v.code.startsWith("{")) continue; // update a variable/field, not a literal
            for (const f of fields) {
              for (const e of this.terms(f.type, j)) {
                if (e.code === `${v.code}.${f.name}`) continue;
                yield mk(`{ ...${v.code}, ${propKey(f.name)}: ${e.code} }`);
              }
            }
          }
        }
        // two-field updates { ...v, f: e1, g: e2 }
        for (const [i, j, l] of splits(size - 1, 3)) {
          for (const v of this.terms(t, i)) {
            if (v.code.startsWith("{")) continue;
            for (let a = 0; a < fields.length; a++) for (let b = a + 1; b < fields.length; b++) {
              const f = fields[a];
              const g = fields[b];
              for (const e1 of this.terms(f.type, j)) for (const e2 of this.terms(g.type, l)) {
                if (e1.code === `${v.code}.${f.name}` || e2.code === `${v.code}.${g.name}`) continue;
                yield mk(`{ ...${v.code}, ${propKey(f.name)}: ${e1.code}, ${propKey(g.name)}: ${e2.code} }`);
              }
            }
          }
        }
        // full literal (fields from small terms)
        if (fields.length && size - 1 >= fields.length) {
          for (const sp of splits(size - 1, fields.length, 3)) {
            const lists = this.parts(fields.map((f) => f.type), sp, 4000, (fi, code) => `${propKey(fields[fi].name)}: ${code}`);
            if (lists) for (const p of product(lists)) yield mk(`{ ${p.join(", ")} }`);
          }
        }
        break;
      }
      case "union": {
        const u = reg.union(t);
        for (const v of u.variants) {
          if (v.fields.length === 0) {
            if (size === 2) yield mk(`{ ${propKey(u.tag)}: ${JSON.stringify(v.lit)} }`);
            continue;
          }
          for (const sp of splits(size - 1, v.fields.length)) {
            const lists = this.parts(v.fields.map((f) => f.type), sp, Infinity, (fi, code) => `${propKey(v.fields[fi].name)}: ${code}`)!;
            for (const p of product(lists)) yield mk(`{ ${propKey(u.tag)}: ${JSON.stringify(v.lit)}, ${p.join(", ")} }`);
          }
        }
        break;
      }
      case "arr": {
        const E = t.elem;
        // [...xs, e]
        for (const [i, j] of splits(size - 1, 2)) for (const xs of this.terms(t, i)) for (const e of this.terms(E, j)) yield mk(`[...${xs.code}, ${e.code}]`);
        // [...xs, ...ys]
        for (const [i, j] of splits(size - 1, 2)) {
          for (const xs of this.terms(t, i)) for (const ys of this.terms(t, j)) {
            if (xs.code === "[]" || ys.code === "[]") continue;
            yield mk(`[...${xs.code}, ...${ys.code}]`);
          }
        }
        // [e]
        for (const e of this.terms(E, size - 1)) yield mk(`[${e.code}]`);
        // [...m.keys()], [...m.values()], [...s]
        for (const [, tt] of this.types) {
          if (tt.k === "map") {
            if (key(tt.key) === key(E)) for (const m of this.terms(tt, size - 1)) yield mk(`[...${wrap(m.code)}.keys()]`);
            if (key(tt.val) === key(E)) for (const m of this.terms(tt, size - 1)) yield mk(`[...${wrap(m.code)}.values()]`);
          }
          if (tt.k === "set" && key(tt.elem) === key(E)) for (const s of this.terms(tt, size - 1)) yield mk(`[...${s.code}]`);
        }
        // (the fields of a record element, or the constrained fields of a type parameter's)
        const elemFields = E.k === "rec" ? reg.rec(E) : E.k === "tvar" ? (E.fields ?? []) : [];
        if (elemFields.length && this.lambdaDepth === 0) {
          const fields = elemFields;
          const keys = fields.filter((f) => ["int", "str", "enum"].includes(f.type.k) && isIdentName(f.name));
          // xs.filter((x) => x.k !== v)
          for (const [i, j] of splits(size - 2, 2)) {
            for (const xs of this.terms(t, i)) {
              if (xs.code.includes("=>")) continue;
              for (const k of keys) for (const v of this.terms(k.type, j)) {
                if (/\bx\b/.test(v.code)) continue;
                yield mk(`${wrap(xs.code)}.filter((x) => x.${k.name} !== ${v.code})`);
                yield mk(`${wrap(xs.code)}.filter((x) => x.${k.name} === ${v.code})`);
              }
            }
          }
          // xs.map((x) => (x.k === v ? { ...x, f: e } : x)) — for records only: a value of a type
          // parameter cannot be rebuilt (the spread is not a T)
          if (E.k === "rec") for (const [i, j, l] of splits(size - 3, 3)) {
            for (const xs of this.terms(t, i)) {
              if (xs.code.includes("=>")) continue;
              for (const k of keys) for (const v of this.terms(k.type, j)) {
                if (/\bx\b/.test(v.code)) continue;
                for (const f of fields) {
                  if (f.name === k.name) continue;
                  for (const e of this.inner(E, f.type, l)) {
                    yield mk(`${wrap(xs.code)}.map((x) => (x.${k.name} === ${v.code} ? { ...x, ${propKey(f.name)}: ${e} } : x))`);
                  }
                }
              }
            }
          }
        }
        break;
      }
      default:
        break;
    }
  }
  /**
   * The options of each part of a call or literal: the terms of `types[i]` at size `sizes[i]`,
   * spelled by `spell`; null when the combinations of all parts but the last outnumber `cap` (those
   * are not built, as before the build was lazy).
   */
  parts(types: readonly VType[], sizes: readonly number[], cap: number, spell: (i: number, code: string) => string): string[][] | null {
    const lists: string[][] = [];
    let n = 1;
    for (let i = 0; i < types.length; i++) {
      lists.push(this.terms(types[i], sizes[i]).map((a) => spell(i, a.code)));
      n *= lists[i].length;
      if (n > cap && i < types.length - 1) return null;
    }
    return lists;
  }
  /** terms of type `ft` over the scope extended with the lambda variable `x : E` */
  inner(E: VType, ft: VType, size: number): string[] {
    const reg = this.prog.reg;
    const xs: Atom[] = [{ code: "x", type: E, size: 1 }];
    if (E.k === "rec") for (const f of reg.rec(E)) if (isIdentName(f.name)) xs.push({ code: `x.${f.name}`, type: f.type, size: 1 });
    if (E.k === "tvar") for (const f of E.fields ?? []) if (isIdentName(f.name)) xs.push({ code: `x.${f.name}`, type: f.type, size: 1 });
    const sub = new Enumerator(this.prog, [...this.scope.filter((a) => !a.code.startsWith("x")), ...xs], ft, size);
    sub.lambdaDepth = 1;
    const r = sub.terms(ft, size).map((a) => a.code).filter((c) => /\bx\b/.test(c) || size === 1);
    if (sub.capped) this.capped = true;
    return r;
  }
}

/** The ways to write n as an ordered sum of `parts` sizes, each between 1 and `max`, lazily (the first part varying slowest). */
function* splits(n: number, parts: number, max = Infinity): Generator<number[]> {
  if (parts < 1 || n < parts || n > max * parts) return;
  if (parts === 1) {
    yield [n];
    return;
  }
  for (let i = 1; i <= Math.min(max, n - parts + 1); i++) for (const rest of splits(n - i, parts - 1, max)) yield [i, ...rest];
}

/** The cartesian product of `lists`, lazily, the first list varying slowest (as nested loops would). */
function* product<A>(lists: readonly (readonly A[])[], i = 0, acc: A[] = []): Generator<A[]> {
  if (i === lists.length) {
    yield [...acc];
    return;
  }
  for (const x of lists[i]) {
    acc.push(x);
    yield* product(lists, i + 1, acc);
    acc.pop();
  }
}

function wrap(code: string): string {
  return /^[\w.$]+$/.test(code) ? code : `(${code})`;
}

/* ───────────────────────── random inputs ───────────────────────── */

// (values well below -1: with -1 the smallest, `a + b + 1 >= a` holds on every sample)
const BASE_INTS = [-10, -5, -2, -1, 0, 0, 1, 1, 2, 3, 4, 5, 7, 10];
const BASE_STRS = ["", "a", "b", "ab", " a ", "hello", "x y"];

/** Constants of the function (contracts included), with their neighbours: boundary values for the tests. */
interface Pools {
  ints: number[];
  strs: string[];
}

function harvest(fn: ts.FunctionDeclaration): Pools {
  const ints = new Set<number>();
  const strs = new Set<string>();
  const visit = (n: ts.Node) => {
    if (ts.isNumericLiteral(n) && /^\d+$/.test(n.text)) {
      const k = Number(n.text) * (ts.isPrefixUnaryExpression(n.parent) && n.parent.operator === ts.SyntaxKind.MinusToken ? -1 : 1);
      for (const d of [-1, 0, 1]) ints.add(k + d);
    }
    if (ts.isStringLiteral(n) && !ts.isLiteralTypeNode(n.parent) && !ts.isImportDeclaration(n.parent)) strs.add(n.text);
    ts.forEachChild(n, visit);
  };
  visit(fn);
  return { ints: [...ints].filter((k) => !BASE_INTS.includes(k)), strs: [...strs].filter((s) => !BASE_STRS.includes(s)) };
}

/**
 * The random numbers of the tests: a seeded generator (mulberry32), so that a run is
 * reproducible. Each hole's tests draw from their own generator, seeded with the run's seed
 * (`--seed N`, default `DEFAULT_SEED`), the function's name and the hole's position: what
 * they say does not depend on the order in which holes are searched. (The tests only filter
 * candidates; Lean proves every fill.)
 */
type Rand = () => number;
export const DEFAULT_SEED = 1;
function seeded(key: string): Rand {
  // FNV-1a of the key, then mulberry32
  let a = 0x811c9dc5;
  for (let i = 0; i < key.length; i++) a = Math.imul(a ^ key.charCodeAt(i), 0x01000193) >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function rnd(rand: Rand, n: number) {
  return Math.floor(rand() * n);
}
const pick = <A>(rand: Rand, xs: A[]): A => xs[rnd(rand, xs.length)];

/**
 * The instantiation of a generic function's type parameters for one test input (by id): `int`
 * or `string` for an unconstrained or equality-constrained parameter, a witness record (the
 * constrained fields and one more) for a field-constrained one.  The function is compiled once
 * (types are erased); Lean proves the fill once for every instantiation.
 */
type Inst = Map<number, VType | "witness">;

function chooseInst(rand: Rand, tparams: readonly TParam[]): Inst {
  return new Map(tparams.map((p) => [p.id, p.fields ? "witness" : rand() < 0.5 ? T.int : T.str]));
}

/** The type of the `id` field of a record type, or of a type parameter's field constraint (null for other types or without one). */
function idField(t: VType, prog: Program): VType | null {
  if (t.k === "tvar") return t.fields?.find((f) => f.name === "id")?.type ?? null;
  if (t.k !== "rec") return null;
  return prog.reg.rec(t).find((f) => f.name === "id")?.type ?? null;
}

function gen(rand: Rand, t: VType, prog: Program, pools: Pools, depth = 0, inst?: Inst): unknown {
  const reg = prog.reg;
  switch (t.k) {
    case "tvar": {
      const c = inst?.get(t.id);
      // (never a silent `undefined`: every value of a type parameter comes from an instantiation)
      if (!c) throw new Error(`internal: no test instantiation of the type parameter ${t.name}`);
      if (c !== "witness") return gen(rand, c, prog, pools, depth, inst);
      const o: Record<string, unknown> = {};
      for (const f of t.fields ?? []) o[f.name] = gen(rand, f.type, prog, pools, depth + 1, inst);
      // (a field the constraint does not name: a fill that rebuilds the value loses it)
      if (!("witness$" in o)) o.witness$ = pick(rand, BASE_STRS);
      return o;
    }
    case "int":
      return pools.ints.length && rand() < 0.4 ? pick(rand, pools.ints) : pick(rand, BASE_INTS);
    case "num":
      return rand() * 10 - 2;
    case "bool":
      return rand() < 0.5;
    case "str":
      return pools.strs.length && rand() < 0.3 ? pick(rand, pools.strs) : pick(rand, BASE_STRS);
    case "enum": {
      const lits = reg.enumLits(t);
      return lits[rnd(rand, lits.length)];
    }
    case "opt": {
      if (rand() >= 0.3) return gen(rand, t.elem, prog, pools, depth, inst);
      const a = (t as OptT).absent ?? "null";
      return a === "undefined" || (a === "both" && rand() < 0.5) ? undefined : null;
    }
    case "tuple":
      return t.elems.map((e) => gen(rand, e, prog, pools, depth, inst));
    case "rec": {
      const o: Record<string, unknown> = {};
      for (const f of reg.rec(t)) o[f.name] = gen(rand, f.type, prog, pools, depth + 1, inst);
      return o;
    }
    case "union": {
      const u = reg.union(t);
      const v = u.variants[rnd(rand, u.variants.length)];
      const o: Record<string, unknown> = { [u.tag]: v.lit };
      for (const f of v.fields) o[f.name] = gen(rand, f.type, prog, pools, depth + 1, inst);
      return o;
    }
    case "arr": {
      const n = depth > 2 ? 0 : rnd(rand, 4);
      const xs = Array.from({ length: n }, () => gen(rand, t.elem, prog, pools, depth + 1, inst));
      // favour distinct ids (common invariant), when the records' (or a type parameter's
      // constrained) `id` is an int (a value of another type, e.g. an enum or a string, would not
      // be a value of the parameter's type)
      if (idField(t.elem, prog)?.k === "int" && xs.length) {
        const ids = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6];
        for (let i = ids.length - 1; i > 0; i--) {
          const j = rnd(rand, i + 1);
          [ids[i], ids[j]] = [ids[j], ids[i]];
        }
        xs.forEach((x, i) => {
          if (x && typeof x === "object" && rand() < 0.9) (x as Record<string, unknown>).id = ids[i];
        });
      }
      return xs;
    }
    case "map": {
      // distinct keys (SameValueZero, as the Map compares them), in a random insertion order
      const m = new Map<unknown, unknown>();
      const n = depth > 2 ? 0 : rnd(rand, 4);
      for (let i = 0; i < n * 2 && m.size < n; i++) {
        const k = gen(rand, t.key, prog, pools, depth + 1, inst);
        if (m.has(k)) continue;
        const v = gen(rand, t.val, prog, pools, depth + 1, inst);
        // values keyed by their own id (a common invariant: m.get(k).id === k), when the id has
        // the key's type (so that the key is a value of the field's type)
        const idT = idField(t.val, prog);
        if (idT && sameType(idT, t.key) && v && typeof v === "object" && rand() < 0.9) (v as Record<string, unknown>).id = k;
        m.set(k, v);
      }
      // sometimes move an entry to the end (delete then set), so the order is not the key order
      if (m.size > 1 && rand() < 0.3) {
        const [k, v] = [...m.entries()][0];
        m.delete(k);
        m.set(k, v);
      }
      return m;
    }
    case "set": {
      const s = new Set<unknown>();
      const n = depth > 2 ? 0 : rnd(rand, 4);
      for (let i = 0; i < n * 2 && s.size < n; i++) s.add(gen(rand, t.elem, prog, pools, depth + 1, inst));
      return s;
    }
    case "unit":
    case "void":
      return undefined;
    case "node":
    case "fn":
      // (never parameters of a function synth fills: the translation rejects them)
      throw new Error(`internal: no test values of type ${showType(t)}`);
    default: {
      // every kind is handled above (tsc checks it): a new kind must say how to test with it
      const k: never = t;
      throw new Error(`internal: no test values of kind ${(k as VType).k}`);
    }
  }
}

/** JSON for counterexample messages: Maps and Sets as their entries (JSON.stringify prints `{}`), undefined spelled out. */
function show(x: unknown): string {
  return JSON.stringify(x, (_k, v) => (v instanceof Map ? { Map: [...v.entries()] } : v instanceof Set ? { Set: [...v] } : v === undefined ? "undefined" : v)) ?? "undefined";
}

/* ───────────────────────── running candidates ───────────────────────── */

/**
 * Evaluates project modules as CommonJS function bodies (no ES module cache:
 * each candidate's module is garbage once its tests ran). Dependencies of the
 * target file are loaded once; `vreact/spec` is the real runtime module.
 */
class Sandbox {
  private cache = new Map<string, Record<string, unknown>>();
  /** dependencies whose top-level code has not finished running (dropped from the cache if it never does) */
  private loading = new Set<string>();
  private spec: Record<string, unknown>;
  constructor(spec: Record<string, unknown>) {
    this.spec = spec;
  }
  static async create(target: string): Promise<Sandbox> {
    let url: string;
    try {
      url = pathToFileURL(createRequire(target).resolve("vreact/spec")).href;
    } catch {
      url = new URL("../spec/index.js", import.meta.url).href;
    }
    return new Sandbox((await import(url)) as Record<string, unknown>);
  }
  private resolveLocal(from: string, spec: string): string | null {
    const base = path.resolve(path.dirname(from), spec);
    const stem = base.replace(/\.(m?[jt]sx?)$/, "");
    for (const c of [base, stem + ".ts", stem + ".tsx", path.join(base, "index.ts"), path.join(base, "index.tsx")]) {
      if (fs.existsSync(c) && fs.statSync(c).isFile()) return c;
    }
    return null;
  }
  private require(from: string, spec: string): unknown {
    if (SPEC_RE.test(spec) || spec === "vreact/spec") return this.spec;
    if (spec.startsWith(".")) {
      const f = this.resolveLocal(from, spec);
      if (f && /\.tsx?$/.test(f)) {
        let m = this.cache.get(f);
        if (!m) {
          m = {};
          // (cached before it runs, for import cycles; as in Node, a module whose top-level code
          // throws is not cached: the next import runs it again, so every candidate sees the same)
          this.cache.set(f, m);
          this.loading.add(f);
          // a dependency's top-level code runs as plain JavaScript (outside test mode), once
          const g = globalThis as Record<string, unknown>;
          const test = g.__VREACT_TEST__;
          g.__VREACT_TEST__ = undefined;
          try {
            this.evalModule(f, fs.readFileSync(f, "utf8").replace(/^\uFEFF/, ""), "", m);
          } catch (e) {
            this.cache.delete(f);
            throw e;
          } finally {
            this.loading.delete(f);
            g.__VREACT_TEST__ = test;
          }
        }
        return m;
      }
      if (!f || !/\.(c?js|json)$/.test(f)) return {}; // stylesheets, images: irrelevant to model functions
      return createRequire(from)(f);
    }
    return createRequire(from)(spec);
  }
  /**
   * Forget the dependencies whose top-level code was cut off (a time limit terminates JavaScript
   * without running its `catch`/`finally` blocks).
   */
  abandonLoading() {
    for (const f of this.loading) this.cache.delete(f);
    this.loading.clear();
  }
  /** Run `text` (TS source of `file`) as a CommonJS module; `epilogue` is appended JS. */
  evalModule(file: string, text: string, epilogue = "", exports: Record<string, unknown> = {}): Record<string, unknown> {
    const { run, module } = this.compileModule(file, text, "", epilogue, exports);
    run();
    return module.exports;
  }
  /**
   * Compile `text` as a CommonJS module without running it: `run()` runs its top-level code.
   * `prologue` is JS that runs first (after a "use strict" directive), where the module's function
   * declarations are already defined (hoisted) and the module object is `CJS_MODULE`; `epilogue`
   * runs last.
   *
   * The module keeps its ES meaning (what Node or a bundler runs): a constant read before its
   * declaration ran throws a ReferenceError also when it is exported (`esmBindings`), and the
   * module's own top-level names — `module`, `exports`, `require`, `__filename`, `__dirname` are
   * legal ones — never meet the CommonJS wrapper's (`cjsNames`).
   */
  compileModule(file: string, text: string, prologue: string, epilogue: string, exports: Record<string, unknown> = {}) {
    let js = ts.transpileModule(esmBindings(text, file), {
      compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, jsx: ts.JsxEmit.ReactJSX, esModuleInterop: true, verbatimModuleSyntax: false },
      fileName: file,
      transformers: { after: [cjsNames] },
    }).outputText;
    if (prologue) {
      const strict = /^\s*"use strict";/.exec(js);
      js = strict ? strict[0] + "\n" + prologue + "\n" + js.slice(strict[0].length) : prologue + "\n" + js;
    }
    const module = { exports };
    const req = (s: string) => this.require(file, s);
    // (the usual CommonJS names too, unless the module declares one of its own: then the wrapper's
    // parameter of that name would be redeclared, a SyntaxError)
    let aliases: [string, unknown][] = [["exports", module.exports], ["require", req], ["module", module], ["__filename", file], ["__dirname", path.dirname(file)]];
    let body: (...a: unknown[]) => unknown;
    try {
      body = new Function(CJS_EXPORTS, CJS_REQUIRE, CJS_MODULE, ...aliases.map(([n]) => n), js + "\n" + epilogue) as typeof body;
    } catch (e) {
      if (!(e instanceof SyntaxError)) throw e;
      aliases = [];
      body = new Function(CJS_EXPORTS, CJS_REQUIRE, CJS_MODULE, js + "\n" + epilogue) as typeof body;
    }
    return { module, run: () => body(module.exports, req, module, ...aliases.map(([, v]) => v)) };
  }
}

/** The CommonJS wrapper's parameters (TypeScript's output refers to them by these names: `cjsNames`). */
const CJS_EXPORTS = "__vreactExports__";
const CJS_REQUIRE = "__vreactRequire__";
const CJS_MODULE = "__vreactModule__";
const CJS_RENAME = new Map([["exports", CJS_EXPORTS], ["require", CJS_REQUIRE], ["module", CJS_MODULE]]);

/**
 * After TypeScript's CommonJS transform: the `exports`, `require` and `module` that the transform
 * itself wrote (identifiers with no source node) become the wrapper's parameters, so that a
 * module-level `const module = …` of the program's (a legal name in an ES module) is a binding of
 * its own, not a redeclaration of the wrapper's parameter (a SyntaxError) or of its exports object.
 */
const cjsNames: ts.TransformerFactory<ts.SourceFile> = (ctx) => (sf) => {
  const f = ts.factory;
  const visit = (n: ts.Node): ts.Node => {
    // (a property name is not a variable: `exports.module = module` keeps its key)
    if (ts.isPropertyAccessExpression(n)) {
      const e = ts.visitNode(n.expression, visit) as ts.Expression;
      return ts.isPropertyAccessChain(n) ? f.updatePropertyAccessChain(n, e, n.questionDotToken, n.name) : f.updatePropertyAccessExpression(n, e, n.name);
    }
    if (ts.isPropertyAssignment(n) && !ts.isComputedPropertyName(n.name)) return f.updatePropertyAssignment(n, n.name, ts.visitNode(n.initializer, visit) as ts.Expression);
    if (ts.isIdentifier(n) && !ts.getParseTreeNode(n)) {
      const to = CJS_RENAME.get(ts.idText(n));
      if (to) return f.createIdentifier(to);
    }
    return ts.visitEachChild(n, visit, ctx);
  };
  return ts.visitNode(sf, visit) as ts.SourceFile;
};

/**
 * `export const A = …, B = …;` becomes `const A = …, B = …;` with `export { A, B };` at the end:
 * the same module for ES semantics, but TypeScript's CommonJS output then reads `A` in the module
 * (a binding that throws a ReferenceError until its declaration ran, as in an ES module) instead of
 * `exports.A` (undefined until then: a read of a constant that the module's top-level code never
 * initialized would pass silently, as `undefined`).
 */
function esmBindings(text: string, file: string): string {
  if (!/\bexport\s+(const|let|var)\b/.test(text)) return text;
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.ES2022, true, file.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
  const edits: Edit[] = [];
  const names: string[] = [];
  for (const st of sf.statements) {
    if (!ts.isVariableStatement(st) || st.modifiers?.some((m) => m.kind === ts.SyntaxKind.DeclareKeyword)) continue;
    const exp = st.modifiers?.find((m) => m.kind === ts.SyntaxKind.ExportKeyword);
    if (!exp || !st.declarationList.declarations.every((d) => ts.isIdentifier(d.name))) continue;
    edits.push({ at: [exp.getStart(sf), exp.getEnd()], text: "" });
    for (const d of st.declarationList.declarations) names.push((d.name as ts.Identifier).text);
  }
  return names.length ? applyEdits(text, edits) + `\nexport { ${names.join(", ")} };\n` : text;
}

interface RunResult {
  ok: boolean;
  valid: number;
  why?: string;
  /** no generated input exercises the hole with this candidate */
  untestable?: string;
  /**
   * ... and that holds whatever the candidate: no input skipped for it evaluated the hole first
   * (the candidate's value could not have decided whether the input reaches another hole, fails
   * the precondition or reads what the module never initialized)
   */
  untestableAll?: boolean;
  /** failure category for the summary */
  cat?: string;
  /**
   * the tests ran out of time: "search", the search's limit (stop); "candidate", this candidate's
   * own cap. `valid` is then the number of inputs it passed before (none failed)
   */
  timeout?: "search" | "candidate";
}

interface Runner {
  /** test `candidate`, in at most `budgetMs` (the search's remaining time) */
  run(candidate: string, budgetMs: number): RunResult;
}

const OWN_ENSURES = "__vreactOwnEnsures__";
const OWN_REQUIRES = "__vreactOwnRequires__";
const TARGET = "__vreactSynthTarget__";
/** called where the tested hole is evaluated (the candidate is tested as `(__vreactHit__(), candidate)`) */
const HIT = "__vreactHit__";
const RUN = "__vreactSynthRun__";
/** at most this long for one candidate's tests (a slower candidate is dropped, and the search goes on) */
const CANDIDATE_MS = 5000;
/** a timed run of the tests: a time limit terminates them, deep inside a candidate's loops too */
const RUN_SCRIPT = new vm.Script(`${RUN}()`);
const OTHER_HOLE = { other: "hole" };
const OWN_PRE = { own: "precondition" };
/** what vreact/spec's hole() throws outside test mode (the contracts are evaluated outside it) */
const isUnfilledHoleError = (e: unknown) => e instanceof Error && e.message.startsWith("vreact: unfilled hole()");
/** reading a module binding whose initialization never ran (the module's top-level code stopped before it) */
const isUninitialized = (e: unknown) => e instanceof ReferenceError && /before initialization/.test(e.message);

function makeRunner(sb: Sandbox, target: string, fname: string, paramTypes: VType[], prog: Program, pools: Pools, textFor: (cand: string) => string, rand: Rand, tparams: readonly TParam[] = []): Runner {
  // fixed sample set (re-used across candidates; counterexamples are moved to the front); the
  // parameters of one input share one instantiation of the type parameters
  const samples: unknown[][] = Array.from({ length: 400 }, () => {
    const inst = chooseInst(rand, tparams);
    return paramTypes.map((t) => gen(rand, t, prog, pools, 0, inst));
  });
  const g = globalThis as Record<string, unknown>;
  const clear = () => {
    g.__VREACT_TEST__ = undefined;
    g[OWN_ENSURES] = undefined;
    g[OWN_REQUIRES] = undefined;
    g[HIT] = undefined;
  };
  // inputs on which the candidate passed so far (what a time limit leaves of a cut-off run)
  let passedSoFar = 0;
  const test = (candidate: string): RunResult => {
    let f: (...a: unknown[]) => unknown;
    let mod: { module: { exports: Record<string, unknown> }; run: () => void };
    try {
      // (the target is taken before the top-level code runs: function declarations are hoisted)
      mod = sb.compileModule(target, textFor(candidate), `${CJS_MODULE}.exports.${TARGET} = ${fname};`, "");
    } catch (e) {
      return { ok: false, valid: 0, why: "does not load: " + (e as Error).message, cat: "does not load" };
    }
    // The module's top-level code may call its functions (`export const TEN: int = inc(9);`): it
    // runs in test mode, where the target's own contract is defined (its requires rejects the
    // input; its ensures are not checked there) and another hole stops it. Code it stops before
    // is never initialized: an input reading it is skipped (it cannot judge the candidate).
    let stopped: string | null = null;
    let hitAtLoad = false;
    g.__VREACT_TEST__ = {
      posts: [],
      fill: () => {
        throw OTHER_HOLE;
      },
    };
    g[OWN_ENSURES] = () => {};
    g[OWN_REQUIRES] = (c: unknown) => {
      if (!c) throw OWN_PRE;
    };
    g[HIT] = () => {
      hitAtLoad = true;
    };
    try {
      mod.run();
    } catch (e) {
      stopped = e === OTHER_HOLE ? "it runs into an unfilled hole" : e === OWN_PRE ? `it calls ${fname} outside its precondition` : `it throws: ${(e as Error)?.message}`;
    } finally {
      clear();
    }
    f = mod.module.exports[TARGET] as typeof f;
    if (typeof f !== "function") return { ok: false, valid: 0, why: `does not load: ${stopped ?? `${fname} is not a function`}`, cat: "does not load" };
    let valid = 0;
    let pre = 0;
    let other = 0;
    let contract = 0;
    let uninit = 0;
    // inputs skipped after the hole was evaluated (the candidate may have decided it)
    let skippedAfterHit = 0;
    for (let i = 0; i < samples.length; i++) {
      const args = structuredClone(samples[i]);
      const own: ((r: unknown) => boolean)[] = [];
      let hit = false;
      g.__VREACT_TEST__ = {
        posts: [], // postconditions of called helpers: not this function's contract
        fill: () => {
          throw OTHER_HOLE;
        },
      };
      g[OWN_ENSURES] = (p: (r: unknown) => boolean) => own.push(p);
      g[OWN_REQUIRES] = (c: unknown) => {
        if (!c) throw OWN_PRE;
      };
      g[HIT] = () => {
        hit = true;
      };
      let r: unknown;
      try {
        r = f(...args);
      } catch (e) {
        if (e === OWN_PRE) {
          pre++;
          if (hit) skippedAfterHit++;
          continue;
        }
        if (e === OTHER_HOLE) {
          other++;
          if (hit) skippedAfterHit++;
          continue;
        }
        if (stopped && isUninitialized(e)) {
          uninit++;
          // (where the candidate ran during the top-level code, it may be why that code stopped)
          if (hit || hitAtLoad) skippedAfterHit++;
          continue;
        }
        samples.unshift(samples.splice(i, 1)[0]);
        if ((e as Error)?.constructor?.name === "PreconditionFailed") return { ok: false, valid, why: `a call violates a precondition on ${show(args)}`, cat: "a call violates a precondition" };
        return { ok: false, valid, why: `throws on ${show(args)}: ${(e as Error)?.message}`, cat: "throws" };
      } finally {
        clear();
      }
      let verdict: "pass" | "fail" | "skip" | "uninit" = "pass";
      for (const p of own) {
        try {
          if (!p(r)) verdict = "fail";
        } catch (e) {
          // the contract calls a function that still has a hole, or reads what the module's
          // top-level code never initialized: this input cannot judge the candidate
          verdict = isUnfilledHoleError(e) ? "skip" : stopped && isUninitialized(e) ? "uninit" : "fail";
        }
        if (verdict !== "pass") break;
      }
      if (verdict === "skip" || verdict === "uninit") {
        if (verdict === "skip") contract++;
        else uninit++;
        if (hit || (verdict === "uninit" && hitAtLoad)) skippedAfterHit++;
        continue;
      }
      valid++;
      if (verdict === "pass") passedSoFar++;
      if (verdict === "fail") {
        samples.unshift(samples.splice(i, 1)[0]); // counterexample first next time
        return { ok: false, valid, why: `postcondition fails on ${show(args)} ↦ ${show(r)}`, cat: "postcondition fails" };
      }
    }
    if (valid > 0) return { ok: true, valid };
    const untestableAll = skippedAfterHit === 0;
    const reasons: string[] = [];
    if (pre) reasons.push(`${pre} fail the precondition of ${fname}`);
    if (other) reasons.push(`${other} reach another unfilled hole`);
    // (not "postcondition fails": the contract cannot be evaluated, e.g. it calls a @trusted stub whose body is a hole)
    if (contract) reasons.push(`on ${contract} the contract of ${fname} runs into a hole (unfinished code it calls)`);
    if (uninit) reasons.push(`${uninit} read what the module's top-level code never initialized (${stopped})`);
    const why =
      pre === samples.length ? `no generated input satisfies the precondition of ${fname} (is it satisfiable?)`
      : `no generated input can test this hole${untestableAll ? "" : ` with this candidate`} (of ${samples.length} inputs, ${reasons.join("; ")})`;
    return { ok: false, valid: 0, why, untestable: why, untestableAll };
  };
  return {
    run(candidate, budgetMs) {
      const ms = Math.max(1, Math.floor(Math.min(CANDIDATE_MS, budgetMs)));
      let res: RunResult | undefined;
      passedSoFar = 0;
      g[RUN] = () => {
        res = test(candidate);
      };
      try {
        RUN_SCRIPT.runInThisContext({ timeout: ms });
      } catch (e) {
        if ((e as { code?: string })?.code !== "ERR_SCRIPT_EXECUTION_TIMEOUT") throw e;
        // (terminated: no `finally` of the tests ran; no input failed before, or they would have
        // stopped there: `valid` is the inputs it passed until then)
        sb.abandonLoading();
        if (budgetMs <= CANDIDATE_MS) return { ok: false, valid: passedSoFar, why: "the search's time limit was reached while it was tested", timeout: "search" };
        return { ok: false, valid: passedSoFar, why: `its tests take longer than ${CANDIDATE_MS / 1000}s`, cat: "too slow to test", timeout: "candidate" };
      } finally {
        clear();
        g[RUN] = undefined;
      }
      return res!;
    },
  };
}

/* ───────────────────────── Lean check ───────────────────────── */

type Status =
  | { status: "proved"; relative: string[] }
  | { status: "rejected"; why: string }
  | { status: "untranslatable"; why: string }
  | { status: "blocked"; why: string }
  | { status: "pending"; why: string };

interface Checked {
  tr: TranslateResult;
  v: Verdict | null;
  diag: string;
}

/* ───────────────────────── search of one hole ───────────────────────── */

interface Survivor {
  code: string;
  valid: number;
  untested?: boolean;
  /** its tests were cut off by a time limit (after `valid` passed inputs) */
  cut?: boolean;
}

/**
 * The enumerate-and-test search of one hole in one context (the fills of the earlier holes it
 * may share an execution with). Lazy and resumable: `next(k)` is the k-th candidate that passes
 * the tests (searching on only when needed), so a search reused under other fills of
 * independent holes yields the same candidates without re-running anything.
 */
interface Search {
  next(k: number): Survivor | null;
  tested: number;
  passed: number;
  sizeReached: number;
  stop: string;
  /** no generated input can test this hole (whatever the candidate, or for the last candidates tested) */
  untestable: string | null;
  /** candidates no input could test, where that depends on the candidate: how many, and the first with its reason */
  deferred: number;
  untestableSome?: string;
  searchMs: number;
  fails: Map<string, { n: number; example: string }>;
  /** the hole works with a Map or Set (its type, its scope's, or their parts) */
  collections: boolean;
}

function newSearch(h: Hole, en: Enumerator, runner: Runner, maxSize: number, limitMs: number): Search {
  const collections = [...en.types.values()].some((t) => t.k === "map" || t.k === "set");
  const S: Search = { next: () => null, tested: 0, passed: 0, sizeReached: 0, stop: "", untestable: null, deferred: 0, searchMs: 0, fails: new Map(), collections };
  const seenText = new Set<string>();
  const seenCanon = new Set<string>();
  // the same candidate up to whitespace and parentheses goes to Lean once
  const fresh = (code: string) => {
    const k = canonical(code);
    if (seenCanon.has(k)) return false;
    seenCanon.add(k);
    return true;
  };
  let untested = 0;
  // candidates that no input could test, where that depends on the candidate (the hole decides
  // whether an input reaches another hole, e.g. an `if` guard): later candidates are still tested,
  // and these go to Lean (or the next hole's search) untested only after the tested survivors
  const deferred: Survivor[] = [];
  let untestableRun = 0;
  // candidates whose tests were cut off by a time limit after they passed some (none failed): held
  // back while the search finds candidates whose tests finish, tried once MAX_CUT_HELD are held or
  // the search ends
  const held: Survivor[] = [];
  function* run(): Generator<Survivor> {
    // search time excludes the Lean checks done while the generator is suspended
    let resume = Date.now();
    const pause = () => {
      S.searchMs += Date.now() - resume;
      resume = -1;
    };
    const left = () => limitMs - (S.searchMs + (Date.now() - resume));
    // the smallest candidates, untested (at most MAX_UNTESTED in all)
    function* untestedOnes(xs: Survivor[]): Generator<Survivor, boolean> {
      for (const sv of xs) {
        if (untested >= MAX_UNTESTED) return false;
        untested++;
        pause();
        yield sv;
        resume = Date.now();
      }
      return true;
    }
    function* release(): Generator<Survivor> {
      for (const sv of held.splice(0)) {
        S.passed++;
        pause();
        yield sv;
        resume = Date.now();
      }
    }
    try {
      search: for (let size = 1; size <= maxSize; size++) {
        S.sizeReached = size;
        for (const c of en.build(h.type, size)) {
          if (left() <= 0) {
            S.stop = `the ${(limitMs / 1000).toFixed(0)}s time limit was reached at size ${size}`;
            break search;
          }
          if (S.tested >= MAX_CANDIDATES) {
            S.stop = `the cap of ${MAX_CANDIDATES} candidates was reached at size ${size}`;
            break search;
          }
          if (seenText.has(c.code)) continue;
          seenText.add(c.code);
          if (S.untestable) {
            // the inputs cannot exercise this hole: the smallest candidates go to Lean untested
            if (untested >= MAX_UNTESTED) {
              S.stop = `${MAX_UNTESTED} untested candidates were tried`;
              break search;
            }
            if (!fresh(c.code)) continue;
            yield* untestedOnes([{ code: c.code, valid: 0, untested: true }]);
            continue;
          }
          S.tested++;
          const r = runner.run(c.code, left());
          if (process.env.VREACT_SYNTH_DEBUG && S.tested <= 12) console.log(`    [${r.ok ? "pass" : "fail"}] ${c.code}  ${r.why ?? ""}`);
          if (r.timeout) {
            if (r.valid > 0) {
              // it passed every input that ran: Lean judges it, after the candidates whose tests finish
              console.log(`  cut off (${r.why}) after passing ${r.valid} random tests: ${c.code}`);
              if (fresh(c.code)) held.push({ code: c.code, valid: r.valid, cut: true });
            } else if (r.timeout === "candidate") {
              // not one input finished in its 5 s: as a candidate no input could test (tried
              // untested, after the tested ones). (One the search's own limit cut off is not: that
              // moment says nothing about it.)
              console.log(`  cut off (${r.why}) before any test finished: ${c.code}`);
              S.untestableSome ??= `${c.code}: ${r.why}, and no test finished before`;
              S.deferred++;
              if (fresh(c.code)) deferred.push({ code: c.code, valid: 0, untested: true });
            }
            if (r.timeout === "search") {
              S.stop = `the ${(limitMs / 1000).toFixed(0)}s time limit was reached at size ${size}, while ${c.code} was tested`;
              break search;
            }
            if (held.length >= MAX_CUT_HELD) yield* release();
            continue;
          }
          if (r.untestable && r.untestableAll) {
            // whatever the candidate (no input evaluated the hole before it was skipped)
            S.untestable = r.untestable;
            console.log(`  ${r.untestable}: the smallest candidates are checked by Lean only`);
            if (!fresh(c.code)) continue;
            yield* untestedOnes([{ code: c.code, valid: 0, untested: true }]);
            continue;
          }
          if (r.untestable) {
            S.untestableSome ??= `${c.code}: ${r.untestable}`;
            S.deferred++;
            if (fresh(c.code)) deferred.push({ code: c.code, valid: 0, untested: true });
            if (++untestableRun < MAX_UNTESTABLE_RUN) continue;
            // no input could test the last MAX_UNTESTABLE_RUN candidates: as for a hole no input
            // can test, the smallest candidates go to Lean untested
            S.untestable = `no generated input could test the last ${MAX_UNTESTABLE_RUN} candidates (e.g. ${S.untestableSome})`;
            console.log(`  ${S.untestable}: the smallest candidates are checked by Lean only`);
            const xs = deferred.splice(0);
            if (!(yield* untestedOnes(xs))) {
              S.stop = `${MAX_UNTESTED} untested candidates were tried`;
              break search;
            }
            continue;
          }
          untestableRun = 0;
          if (!r.ok) {
            const cat = r.cat ?? "fails";
            const e = S.fails.get(cat) ?? { n: 0, example: `${c.code}: ${r.why}` };
            e.n++;
            S.fails.set(cat, e);
            continue;
          }
          if (!fresh(c.code)) continue;
          S.passed++;
          pause();
          yield { code: c.code, valid: r.valid };
          resume = Date.now();
        }
      }
      if (!S.stop) S.stop = `all candidates up to size ${maxSize} were tried` + (en.capped ? ` (sub-expression lists were capped at ${MAX_TERMS} per type and size, so some larger candidates were never built)` : "");
      if (held.length) {
        console.log(`  ${held.length} candidate(s) whose tests were cut off after they passed some: tried now`);
        yield* release();
      }
      if (deferred.length) {
        // the candidates the inputs could not test, after every tested survivor
        console.log(`  ${S.deferred} candidate(s) could not be tested (e.g. ${S.untestableSome}): the smallest go to Lean untested`);
        yield* untestedOnes(deferred.splice(0));
      }
    } finally {
      if (resume >= 0) pause();
    }
  }
  const it = run();
  const found: Survivor[] = [];
  let done = false;
  S.next = (k) => {
    while (found.length <= k && !done) {
      const r = it.next();
      if (r.done) done = true;
      else found.push(r.value);
    }
    return found[k] ?? null;
  };
  return S;
}

/* ───────────────────────── command ───────────────────────── */

export { Enumerator, mayShareExecution, canonical };

export interface SynthResult {
  fn: string;
  hole: string;
  solution: string | null;
  tested: number;
  /** Lean proved the function with this fill (`status` says whether that proof assumes anything) */
  proved: boolean;
  /**
   * proved: by Lean, with only the standard axioms; proved-relative: by Lean, assuming the
   * declarations in `relative_to` (@trusted contracts, assume(…) facts); not-proved; skipped
   */
  status: string;
  /** the non-standard axioms the proof relies on (proved-relative only) */
  relative_to?: string[];
  note?: string;
}

export async function synthCommand(root: string, files: string[], opts: { write?: boolean; json?: boolean; maxSize?: number; seed?: number; timeLimitMs?: number }): Promise<SynthResult[]> {
  if (!files.length) throw new Error("usage: vreact synth <file.tsx> [--write]");
  const cfg = loadConfig(root);
  const maxSize = opts.maxSize ?? 9;
  // the search time of one hole (tests may lower it)
  const timeLimitMs = opts.timeLimitMs ?? TIME_LIMIT_MS;
  const seed = opts.seed ?? DEFAULT_SEED;
  // the file as the program knows it (same spelling as cfg.files: case-insensitive file systems, symlinks)
  const typed = path.resolve(root, files[0]);
  const real = (f: string) => fs.realpathSync.native(f);
  const target = fs.existsSync(typed) ? cfg.files.find((f) => fs.existsSync(f) && real(f) === real(typed)) : undefined;
  if (!target) {
    console.log(fs.existsSync(typed) ? `✗ ${files[0]} is not one of the project's VTS files (see "src"/"include"/"exclude" in vreact.json)` : `✗ ${files[0]}: no such file`);
    process.exitCode = 1;
    return [];
  }
  // (the default seed is not mentioned: the output of a run without --seed stays as it was)
  if (opts.seed !== undefined) console.log(`random tests from seed ${seed}`);
  const rel = path.relative(root, target);
  const raw = fs.readFileSync(target, "utf8");
  // offsets are computed on the text without a byte-order mark; the mark is restored on --write
  const bom = raw.startsWith("﻿") ? "﻿" : "";
  const base = raw.slice(bom.length);
  const results: SynthResult[] = [];
  const fmtErr = (e: VtsError) => `${e.file ? path.relative(root, e.file) : "?"}:${e.line}:${e.col}: ${e.message}`;

  // ---- Lean checks of in-memory texts ----
  const checks = new Map<string, Checked>();
  const check = (text: string): Checked => {
    let c = checks.get(text);
    if (!c) {
      const tr = translate({ ...cfg, overrides: new Map([[target, text]]) } as Config);
      if (!tr.ok) c = { tr, v: null, diag: [...tr.tsDiagnostics, ...tr.errors.map(fmtErr)].join("; ") };
      else {
        const lk = runLake(cfg.outDir, cfg.leanLib);
        c = { tr, v: judge(tr.obligations, lk.messages, findMarkers(cfg.outDir), cfg.outDir), diag: "" };
      }
      checks.set(text, c);
    }
    return c;
  };

  // ---- the program must translate before synthesis (holes are fine: they become sorry);
  // the translator also reports the narrowing in effect at each hole ----
  const holeEnvs: HoleEnv[] = [];
  const baseTr = translate({ ...cfg, overrides: new Map([[target, base]]), holeEnvs } as Config);
  if (!baseTr.ok) {
    console.log("synth needs a project that translates (holes may stay); fix these first:");
    for (const d of [...baseTr.tsDiagnostics, ...baseTr.errors.map(fmtErr)]) console.log("  " + d);
    process.exitCode = 1;
    return results;
  }
  const narrowings = narrowingAtHoles(holeEnvs);

  // ---- program, holes, tasks ----
  const options: ts.CompilerOptions = { strict: true, jsx: ts.JsxEmit.ReactJSX, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, skipLibCheck: true, noEmit: true, allowImportingTsExtensions: true };
  const program = ts.createProgram(cfg.files, options, overrideHost(options, new Map([[target, base]])));
  const checker = program.getTypeChecker();
  // (the translator's module names, so that type names agree with the translation's)
  const prog = new Program(program, root, (sf) => moduleNs(cfg.srcDir, sf.fileName), cfg.files.map((f) => program.getSourceFile(f)).filter((x) => !!x));
  const sf = program.getSourceFile(target)!;
  const env = baseEnv(new ModCtx(prog, "VTS.Synth", sf, [], { n: 0 }));
  const isTrusted = (n: ts.Node) => ts.getJSDocTags(n).some((t) => t.tagName.text === "trusted");
  for (const st of sf.statements) {
    if (!ts.isTypeAliasDeclaration(st) && !ts.isInterfaceDeclaration(st)) continue;
    try {
      typeOfDecl(st, prog.typeEnv);
    } catch {
      /* not needed unless a hole uses it (then the error shows up there) */
    }
  }
  // the type parameters of generic functions (their signatures and holes mention them)
  const tparamsOf = new Map<ts.FunctionDeclaration, TParam[]>();
  for (const st of sf.statements) {
    if (!ts.isFunctionDeclaration(st) || !st.typeParameters?.length || isComponentDecl(st, prog)) continue;
    try {
      const tps = registerTypeParams(st, prog.typeEnv);
      // the absent value of an optional constrained field (`note?: string`: undefined, never
      // null), as for the fields of registered records (annotateRegistry)
      for (const p of tps) for (const f of p.fields ?? []) annotateOpt(f.type, p.fieldTs.get(f.name), checker);
      tparamsOf.set(st, tps);
    } catch (e) {
      if (!(e instanceof VtsError)) throw e; /* reported by the translation */
    }
  }
  const holeCalls: ts.CallExpression[] = [];
  const findHoles = (n: ts.Node, into: ts.CallExpression[]) => {
    if (ts.isCallExpression(n) && specFn(env, n.expression) === "hole") into.push(n);
    ts.forEachChild(n, (c) => findHoles(c, into));
  };
  findHoles(sf, holeCalls);
  if (!holeCalls.length) console.log(`no hole<T>() in ${rel}`);
  const skipped = (fn: string, hole: string, note: string) => {
    console.log(`  ✗ ${note}`);
    results.push({ fn, hole, solution: null, tested: 0, proved: false, status: "skipped", note });
  };
  const tasks: Task[] = [];
  const sigHint = (fn: ts.FunctionDeclaration, p: ts.ParameterDeclaration) => capitalize(fn.name!.text) + capitalize(ts.isIdentifier(p.name) ? p.name.text : "Param");
  const paramTypes = (fn: ts.FunctionDeclaration): Map<string, VType> => {
    const m = new Map<string, VType>();
    for (const p of fn.parameters) {
      if (!ts.isIdentifier(p.name) || !p.type) continue;
      const t = typeOfNode(p.type, prog.typeEnv, sigHint(fn, p));
      annotateOpt(t, checker.getTypeFromTypeNode(p.type), checker, !!p.questionToken);
      m.set(p.name.text, t);
    }
    return m;
  };
  holeCalls.forEach((node, index) => {
    let fn: ts.Node = node;
    while (fn && !(ts.isFunctionDeclaration(fn) && ts.isSourceFile(fn.parent))) fn = fn.parent;
    const { line } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    const where = `${rel}:${line + 1}`;
    if (!fn) {
      console.log(`hole at ${where}`);
      return skipped("?", "?", `${where}: synth fills holes inside top-level functions only`);
    }
    const fd = fn as ts.FunctionDeclaration;
    const name = fd.name?.text ?? "?";
    let task = tasks.find((t) => t.fn === fd);
    // a hole inside a contract call of the function (its requires/ensures, an assert, …)
    let call: string | null = null;
    for (let n: ts.Node = node.parent; n && n !== fd && !call; n = n.parent) {
      const k = ts.isCallExpression(n) ? specFn(env, n.expression) : null;
      if (k && CONTRACT_FNS.has(k)) call = k;
    }
    if (call) {
      if (!task) tasks.push((task = { fn: fd, name, holes: [], ensures: 0, contractHoles: [] }));
      task.contractHoles.push({ where, call, type: node.typeArguments?.[0] ? node.typeArguments[0].getText(sf) : "?" });
      return;
    }
    if (!node.typeArguments?.[0]) {
      console.log(`hole in ${name}`);
      return skipped(name, "?", `${where}: write hole<T>() with an explicit type`);
    }
    let type: VType;
    try {
      type = typeOfNode(node.typeArguments[0], prog.typeEnv, "Hole");
      annotateOpt(type, checker.getTypeFromTypeNode(node.typeArguments[0]), checker);
    } catch (e) {
      if (!(e instanceof VtsError)) throw e;
      console.log(`hole in ${name}`);
      return skipped(name, "?", `${where}: ${e.message}`);
    }
    if (!task) tasks.push((task = { fn: fd, name, holes: [], ensures: 0, contractHoles: [] }));
    task.holes.push({ index, node, span: [node.getStart(sf), node.getEnd()], type, fn: fd, scope: [], parens: needsParens(node) });
  });

  // functions referenced (transitively) from a node, any file of the program
  const refsCache = new Map<ts.Node, Set<ts.FunctionDeclaration>>();
  const refsFrom = (node: ts.Node, self?: ts.FunctionDeclaration): Set<ts.FunctionDeclaration> => {
    const out = new Set<ts.FunctionDeclaration>();
    const visit = (n: ts.Node) => {
      if (ts.isIdentifier(n)) {
        let s = refSymbol(checker, n);
        if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
        const dd = s?.declarations?.[0];
        if (dd && dd !== self && ts.isFunctionDeclaration(dd) && ts.isSourceFile(dd.parent) && !out.has(dd)) {
          out.add(dd);
          for (const x of refsOf(dd)) out.add(x);
        }
      }
      ts.forEachChild(n, visit);
    };
    visit(node);
    return out;
  };
  // functions referenced (transitively) by a declaration
  const refsOf = (d: ts.FunctionDeclaration): Set<ts.FunctionDeclaration> => {
    const done = refsCache.get(d);
    if (done) return done;
    const out = new Set<ts.FunctionDeclaration>();
    refsCache.set(d, out);
    if (d.body) for (const x of refsFrom(d.body, d)) out.add(x);
    return out;
  };
  /**
   * The functions that a node depends on, transitively: for each function it names, that
   * function's `requires` and its body without the contract, but not its `ensures` (separate
   * theorems that a statement never mentions; at run time, a callee's ensures are recorded and
   * ignored). `lean`: what the node's Lean translation mentions through types and values (what
   * `#print axioms` follows), where a @trusted function is an axiom whose type has the `requires`
   * (the `h_pre` binder) but which has no value; otherwise what runs, @trusted bodies included.
   */
  const dependsOn = (lean: boolean) => {
    const cache = new Map<ts.FunctionDeclaration, Set<ts.FunctionDeclaration>>();
    const from = (node: ts.Node, self: ts.FunctionDeclaration | undefined, out = new Set<ts.FunctionDeclaration>()): Set<ts.FunctionDeclaration> => {
      const visit = (n: ts.Node) => {
        if (ts.isIdentifier(n)) {
          let s = refSymbol(checker, n);
          if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
          const dd = s?.declarations?.[0];
          if (dd && dd !== self && ts.isFunctionDeclaration(dd) && ts.isSourceFile(dd.parent) && !out.has(dd)) {
            out.add(dd);
            for (const x of of(dd)) out.add(x);
          }
        }
        ts.forEachChild(n, visit);
      };
      visit(node);
      return out;
    };
    const of = (d: ts.FunctionDeclaration): Set<ts.FunctionDeclaration> => {
      const done = cache.get(d);
      if (done) return done;
      const out = new Set<ts.FunctionDeclaration>();
      cache.set(d, out);
      const stmts = d.body?.statements ?? [];
      let i = 0;
      for (; i < stmts.length; i++) {
        const st = stmts[i];
        if (!ts.isExpressionStatement(st) || !ts.isCallExpression(st.expression)) break;
        const k = specFn(env, st.expression.expression);
        if (k === "requires") from(st, d, out);
        else if (k !== "ensures" && k !== "decreases") break;
      }
      if (!(lean && isTrusted(d))) for (const st of stmts.slice(i)) from(st, d, out);
      return out;
    };
    return { from, of };
  };
  const leanDeps = dependsOn(true);
  const runDeps = dependsOn(false);
  /**
   * The functions that a contract of the program depends on (a `requires`, `ensures`, `assert`, …
   * anywhere, in any of its files: what its Lean statement mentions), each with the first such
   * contract. A fill of one changes what that contract says.
   */
  const contractUse = new Map<ts.FunctionDeclaration, string>();
  for (const f of cfg.files) {
    const file = program.getSourceFile(f);
    if (!file) continue;
    const visit = (n: ts.Node) => {
      const k = ts.isCallExpression(n) ? specFn(env, n.expression) : null;
      if (k && CONTRACT_FNS.has(k)) {
        let owner: ts.Node | undefined = n.parent;
        while (owner && !(ts.isFunctionDeclaration(owner) && ts.isSourceFile(owner.parent))) owner = owner.parent;
        const ownerFn = owner as ts.FunctionDeclaration | undefined;
        const where = ownerFn ? `the ${k}(…) of ${ownerFn.name?.text ?? "a function"}` : `a module-level ${k}(…)${file === sf ? "" : ` in ${path.relative(root, file.fileName)}`}`;
        for (const d of leanDeps.from(n, ownerFn)) if (!contractUse.has(d)) contractUse.set(d, where);
        return;
      }
      ts.forEachChild(n, visit);
    };
    visit(file);
  }
  const holesIn = (d: ts.FunctionDeclaration) => {
    const hs: ts.CallExpression[] = [];
    if (d.body) findHoles(d.body, hs);
    return hs;
  };
  // callees first: a function's proof can only be complete once the functions it calls are
  const ordered: Task[] = [];
  const visitTask = (t: Task, stack: Set<Task>) => {
    if (ordered.includes(t) || stack.has(t)) return;
    stack.add(t);
    for (const d of refsOf(t.fn)) {
      const u = tasks.find((x) => x.fn === d);
      if (u) visitTask(u, stack);
    }
    ordered.push(t);
  };
  // and first of all the functions that the module's top-level code runs (constant initializers,
  // module-level asserts): while one has a hole, that code stops there when the module loads in the
  // tests, and the constants declared after it stay uninitialized for every other function's tests
  // (an input that reads one cannot judge a candidate)
  const runAtLoad = new Set<ts.FunctionDeclaration>();
  for (const st of sf.statements) if (!ts.isFunctionDeclaration(st) && !ts.isImportDeclaration(st) && !ts.isTypeAliasDeclaration(st) && !ts.isInterfaceDeclaration(st)) runDeps.from(st, undefined, runAtLoad);
  for (const t of tasks) if (runAtLoad.has(t.fn)) visitTask(t, new Set());
  for (const t of tasks) visitTask(t, new Set());

  const sb = holeCalls.length ? await Sandbox.create(target) : null;
  const accepted = new Map<Hole, string>(); // proved fills (text inserted at the hole)
  const acceptedTasks: Task[] = [];
  const editsOf = (fills: Map<Hole, string>): Edit[] => [...fills].map(([h, text]) => ({ at: h.span, text }));
  // (what the original text uses: only a binding a fill left without a use is dropped)
  const baseUsed = new Map(bindingsOf(base, target).bindings.map((b) => [b.key, b.used]));
  const leanText = (fills: Map<Hole, string>) => dropUnusedAfterFill(applyEdits(base, editsOf(fills)), target, (k) => !!baseUsed.get(k));
  /** the functions among `ds` whose Lean definition still has a hole (`sorry`): not filled by `fills`, not @trusted (axiomatized) */
  const unfinished = (ds: Iterable<ts.FunctionDeclaration>, fills: Map<Hole, string>) => [...ds].filter((d) => !isTrusted(d) && holesIn(d).some((h) => ![...fills.keys()].some((x) => x.node === h)));
  /** a function whose body still has a hole that no proved fill replaces (@trusted or not: the tests run its body) */
  const unfilled = (d: ts.FunctionDeclaration) => holesIn(d).some((h) => ![...accepted.keys()].some((x) => x.node === h));
  const fnNames = (ds: ts.FunctionDeclaration[]) => ds.map((d) => d.name?.text ?? "?").join(", ");

  // the status of task `t` in a checked text
  const statusOf = (c: Checked, text: string, t: Task, fills: Map<Hole, string>): Status => {
    if (!c.v) return { status: "untranslatable", why: c.diag };
    const v = c.v;
    const mr = c.tr.modules.find((m) => path.resolve(m.tsFile) === path.resolve(target));
    const fi = mr?.functions.find((f) => f.name === t.name);
    if (!fi) return { status: "blocked", why: `internal: ${t.name} not found in the Lean translation of ${rel}: nothing to check` };
    const tsf = ts.createSourceFile(target, text, ts.ScriptTarget.ES2022, true, target.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
    const decl = tsf.statements.find((s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && s.name?.text === t.name);
    if (!decl) return { status: "blocked", why: `internal: ${t.name} not found in the candidate text` };
    const lo = tsf.getLineAndCharacterOfPosition(decl.getStart(tsf)).line + 1;
    const hi = tsf.getLineAndCharacterOfPosition(decl.getEnd()).line + 1;
    const own = new Set(c.tr.obligations.filter((ob) => path.resolve(ob.file) === path.resolve(target) && ob.line >= lo && ob.line <= hi).map((ob) => ob.id));
    const failedOwn = v.failed.filter((f) => own.has(f.ob.id));
    if (failedOwn.length) return { status: "rejected", why: failedOwn.map((f) => `${f.ob.desc} (${f.ob.where})`).join("; ") };
    if (v.internal.length) {
      const i = v.internal[0];
      return { status: "blocked", why: `Lean reports internal errors in the generated code (${v.internal.length}), e.g. ${i.file}:${i.line}: ${i.text.split("\n")[0]}` };
    }
    const names = [fi.qname, ...fi.posts];
    if (fi.posts.length !== t.ensures) return { status: "blocked", why: `internal: ${t.name} has ${t.ensures} ensures but ${fi.posts.length} postcondition theorem(s) in Lean` };
    const unchecked = names.filter((q) => !v.axioms.has(q));
    if (unchecked.length || v.unchecked.some((ob) => own.has(ob.id))) {
      const other = v.failed[0];
      const cause = other ? `${other.ob.where} [${other.ob.kind}] ${other.ob.desc} fails, so the module was not fully checked` : "a module it depends on did not build";
      return { status: "blocked", why: `Lean did not check ${t.name} and its postcondition(s): ${cause} (fix that first)` };
    }
    if (names.some((q) => v.axioms.get(q)!.includes("sorryAx"))) {
      const pending = unfinished(refsOf(t.fn), fills).map((d) => d.name?.text ?? "?");
      return { status: "pending", why: pending.length ? `its proof depends on unfinished code (hole) in ${pending.join(", ")}` : `its proof depends on a sorry (a hole or an unfinished proof it relies on)` };
    }
    // `VReact.assumed` is an assume(…) of the program only where `#vreact_assumed` found no
    // user-proof declaration using it directly (see cli.ts `classify`); those are listed too
    const assumedIn = names.filter((q) => v.axioms.get(q)!.some((a) => a === "VReact.assumed" || a === "assumed"));
    const noAudit = assumedIn.find((q) => !v.assumedOutside.has(q));
    if (noAudit !== undefined) return { status: "blocked", why: `Lean printed no \`#vreact_assumed\` report for ${noAudit}, which relies on VReact.assumed: not checked` };
    const viaProofs = assumedIn.flatMap((q) => v.assumedOutside.get(q)!).map((d) => `${d} (a user proof using VReact.assumed directly)`);
    const relative = [...new Set([...names.flatMap((q) => v.axioms.get(q)!), ...viaProofs])].filter((a) => !STD_AXIOMS.has(a));
    return { status: "proved", relative };
  };
  /**
   * The functions of the target module that the fill texts call and whose Lean declarations rest
   * on a sorry (a failed obligation of theirs, admitted, or a hole): a candidate calling one is
   * "pending" because of its own choice of helper, not because of the function being filled.
   */
  const sorryCallees = (c: Checked, fills: string[]): string[] => {
    if (!c.v) return [];
    const mr = c.tr.modules.find((m) => path.resolve(m.tsFile) === path.resolve(target));
    const called = new Set<string>();
    for (const code of fills) {
      const visit = (n: ts.Node) => {
        if (ts.isCallExpression(n) && ts.isIdentifier(n.expression)) called.add(n.expression.text);
        ts.forEachChild(n, visit);
      };
      visit(ts.createSourceFile("c.ts", `(${code});`, ts.ScriptTarget.ES2022, true));
    }
    return [...called].filter((nm) => {
      const fi = mr?.functions.find((f) => f.name === nm);
      return !!fi && [fi.qname, ...fi.posts].some((q) => !c.v!.axioms.has(q) || c.v!.axioms.get(q)!.includes("sorryAx"));
    });
  };
  const callsAny = (code: string, names: Set<string>) => [...names].some((nm) => new RegExp(`(^|[^\\w$.])${nm.replace(/\$/g, "\\$")}\\(`).test(code));
  /** the holes whose fills in `fills` call one of `names` */
  const taintedBy = (fills: Map<Hole, string>, names: Set<string>) => [...fills].filter(([, c]) => callsAny(c, names)).map(([x]) => x);
  const provedStatus = (relative: string[]) => (relative.length ? "proved-relative" : "proved");
  const relNote = (relative: string[]) => `proved assuming ${relative.join(", ")} (@trusted contracts, assume(…) facts or axioms of user proofs, not proved)`;

  for (const task of ordered) {
    const fd = task.fn;
    const n = task.holes.length;
    const holesLabel = n > 1 ? `${n} holes in ${task.name}` : `hole in ${task.name}`;
    const record = (h: Hole, solution: string | null, tested: number, status: string, note?: string, relative?: string[]) => {
      results.push({ fn: task.name, hole: showType(h.type), solution, tested, proved: status === "proved" || status === "proved-relative", status, ...(relative?.length ? { relative_to: relative } : {}), note });
    };
    if (task.contractHoles.length) {
      const c = task.contractHoles[0];
      const more = task.contractHoles.length > 1 ? ` (and ${task.contractHoles.length - 1} more)` : "";
      console.log(n ? holesLabel : `hole in ${task.name}`);
      const why = `${c.where}: a hole inside ${c.call}(…)${more} is part of the contract of ${task.name}, the specification its holes are filled against: synth never fills it (a fill proved against the contract it is part of could be vacuous, e.g. requires(false)); write the contract by hand`;
      for (const ch of task.contractHoles) results.push({ fn: task.name, hole: ch.type, solution: null, tested: 0, proved: false, status: "skipped", note: why });
      for (const h of task.holes) record(h, null, 0, "skipped", why);
      console.log(`  ✗ not searched: ${why}`);
      continue;
    }
    if (isTrusted(fd)) {
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", "@trusted");
      console.log(`  ✗ ${task.name} is /** @trusted */: Lean checks nothing in its body, so a fill could not be proved. Remove @trusted to synthesize it.`);
      continue;
    }
    if (isComponentDecl(fd, prog)) {
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", "component");
      console.log(`  ✗ ${task.name} looks like a component: synth fills holes in model functions; move the expression into one`);
      continue;
    }
    // types, scope, helpers
    let params: Map<string, VType>;
    const helpers: Helper[] = [];
    const genericHelpers: GenericHelper[] = [];
    try {
      params = paramTypes(fd);
      for (const h of task.holes) h.scope = holeScope(narrowings.get(`${path.resolve(target)}:${h.span[0]}`) ?? new Map(), prog, params);
      for (const st of sf.statements) {
        if (!ts.isFunctionDeclaration(st) || !st.name || st === fd || !st.type) continue;
        if (/^[A-Z]/.test(st.name.text)) continue;
        const hasPre = st.body?.statements.some((x) => ts.isExpressionStatement(x) && ts.isCallExpression(x.expression) && specFn(env, x.expression.expression) === "requires");
        // (a function whose holes were filled above is a helper like any other; one that calls
        // this function is not: VTS has no recursion, so such a fill would never translate; nor
        // one that runs into a hole, e.g. a @trusted stub calling unfinished code: no input could
        // test a candidate calling it, and the first such candidate would make the hole look untestable)
        if (hasPre || st.parameters.some((p) => !p.type) || refsOf(st).has(fd) || [st, ...runDeps.of(st)].some(unfilled)) continue;
        if (st.typeParameters?.length) {
          // a generic helper: offered at instantiations from the hole's types (searchOf)
          const tps = tparamsOf.get(st);
          if (!tps) continue;
          try {
            const gh: GenericHelper = {
              name: st.name.text,
              params: st.parameters.map((p) => typeOfNode(p.type!, prog.typeEnv, sigHint(st, p))),
              ret: typeOfNode(st.type, prog.typeEnv, capitalize(st.name.text) + "Result"),
              tparams: tps,
              paramTs: st.parameters.map((p) => checker.getTypeFromTypeNode(p.type!)),
              retTs: checker.getTypeFromTypeNode(st.type),
            };
            // (only where the arguments determine every type parameter: the candidate is written
            // without type arguments, and the translator infers them from the arguments' types)
            if (tps.every((p) => gh.params.some((t) => mentionsTVar(t, new Set([p.id]))))) genericHelpers.push(gh);
          } catch (e) {
            if (!(e instanceof VtsError)) throw e; /* unsupported signature: not a helper */
          }
          continue;
        }
        try {
          const h = { name: st.name.text, params: st.parameters.map((p) => typeOfNode(p.type!, prog.typeEnv, sigHint(st, p))), ret: typeOfNode(st.type, prog.typeEnv, capitalize(st.name.text) + "Result") };
          st.parameters.forEach((p, i) => annotateOpt(h.params[i], checker.getTypeFromTypeNode(p.type!), checker));
          annotateOpt(h.ret, checker.getTypeFromTypeNode(st.type), checker);
          helpers.push(h);
        } catch (e) {
          if (!(e instanceof VtsError)) throw e; /* unsupported signature: not a helper */
        }
      }
      annotateRegistry(prog, checker);
    } catch (e) {
      if (!(e instanceof VtsError)) throw e;
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", e.message);
      console.log(`  ✗ cannot synthesize ${task.name}: ${fmtErr(e)}`);
      continue;
    }
    const pTypes = fd.parameters.map((p) => (ts.isIdentifier(p.name) ? params.get(p.name.text) : undefined));
    if (pTypes.some((t) => !t)) {
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", "parameters");
      console.log(`  ✗ cannot synthesize ${task.name}: every parameter needs a name and a type annotation`);
      continue;
    }
    // the function's own contract, renamed for the test harness (helpers' contracts are not this function's)
    const ownContract: Edit[] = [];
    const contractStmts: ts.Statement[] = [];
    for (const st of fd.body?.statements ?? []) {
      if (!ts.isExpressionStatement(st) || !ts.isCallExpression(st.expression)) break;
      const callee = st.expression.expression;
      const k = specFn(env, callee);
      if (k === "ensures") {
        ownContract.push({ at: [callee.getStart(sf), callee.getEnd()], text: OWN_ENSURES });
        task.ensures++;
      } else if (k === "requires") ownContract.push({ at: [callee.getStart(sf), callee.getEnd()], text: OWN_REQUIRES });
      else if (k !== "decreases") break;
      contractStmts.push(st);
    }
    // a function that a contract depends on, with no ensures of its own: Lean checks its fill against
    // nothing, so any fill (the smallest: `true`, `0`) would be "proved" — and would become part of
    // that contract (an ensures that says nothing, a requires that rules out every input). Like a
    // hole inside a contract, it is the specification: not filled
    const usedBy = contractUse.get(fd);
    if (usedBy && task.ensures === 0) {
      const why = `${task.name} has no ensures and ${usedBy} calls it (directly or through other functions): Lean would check a fill of ${task.name} against no postcondition, so any fill (the smallest first: \`true\`, \`0\`) would be "proved" and would become part of that contract: synth does not fill it; give ${task.name} an ensures that says what it computes, or write it by hand`;
      console.log(`${holesLabel}`);
      console.log(`  ✗ not searched: ${why}`);
      for (const h of task.holes) record(h, null, 0, "skipped", why);
      continue;
    }
    // a contract whose Lean statement mentions a function with a hole cannot be proved (its
    // theorems then depend on that function's `sorry`) until that function is finished. Only what
    // the statement mentions counts: not the bodies of @trusted callees (axioms) nor the ensures of
    // callees; anything else a proof may use is left to Lean (status "pending")
    const contractNeeds = unfinished(new Set(contractStmts.flatMap((st) => [...leanDeps.from(st, fd)]).filter((d) => d !== fd)), accepted);
    if (contractNeeds.length) {
      const why = `the contract of ${task.name} depends on unfinished function${contractNeeds.length > 1 ? "s" : ""} ${fnNames(contractNeeds)} (a hole remains): finish ${contractNeeds.length > 1 ? "them" : "it"} first`;
      console.log(`${holesLabel}`);
      console.log(`  ✗ not searched: ${why}`);
      for (const h of task.holes) record(h, null, 0, "not-proved", why);
      continue;
    }
    const pools = harvest(fd);
    const t0All = Date.now();
    // time for the whole function: the per-hole limit for each hole, and one more for backtracking
    const deadline = t0All + timeLimitMs * (n + 1);
    const leanBudget = MAX_LEAN_CHECKS * n;
    let leanRuns = 0;
    let blocked: string | null = null; // no fill of this function can be checked now
    let halt: string | null = null; // this function's time or Lean-check budget is spent
    let provedRelative: string[] = [];
    // helpers whose proofs rest on a sorry (found by Lean checks of candidates calling them)
    const sorryHelpers = new Set<string>();
    const notes = new Map<Hole, { tested: number; last?: string; cand?: string }>();
    // deps[i]: the earlier holes that a call reaching hole i may also evaluate (only their fills
    // can change what the tests of hole i say)
    const recursive = callsItself(fd, checker, refsOf(fd));
    const deps = task.holes.map((h, i) => new Set(task.holes.slice(0, i).flatMap((x, j) => (mayShareExecution(x.node, h.node, fd, recursive) ? [j] : []))));
    const searches = new Map<string, Search>();
    const searchOf = (i: number, ctx: Map<Hole, string>): Search => {
      const h = task.holes[i];
      const en = new Enumerator(prog, h.scope, h.type, maxSize);
      // generic helpers at the types the hole works with (its type, its scope's types and their
      // parts), before the monomorphic helpers add theirs
      const holeTypes = [...en.types.values()];
      const insts: Helper[] = genericHelpers.flatMap((gh) => instantiateHelper(gh, holeTypes, prog.reg, checker));
      for (const hp of [...helpers, ...insts]) {
        en.helpers.push(hp);
        hp.params.forEach((t) => en.register(t));
      }
      // the earlier holes this one cannot share a call with stay unfilled (calls reaching them are skipped)
      // (the hole's own random inputs: the same whatever the earlier fills and the search order)
      const rand = seeded(`${seed}\u0000${task.name}\u0000${i}`);
      const runner = makeRunner(sb!, target, task.name, pTypes as VType[], prog, pools, (cand) => applyEdits(base, [...editsOf(new Map([...accepted, ...ctx, [h, `(${HIT}(), ${cand})`]])), ...ownContract]), rand, tparamsOf.get(fd) ?? []);
      return newSearch(h, en, runner, maxSize, Math.min(timeLimitMs, Math.max(Math.min(5000, timeLimitMs), deadline - Date.now())));
    };

    /** `failed`: the hole whose search failed; `told`: the backjump was reported */
    type Outcome = { sol: Map<Hole, string> | null; conflict: Set<number>; failed?: number; told?: boolean };
    /**
     * Search hole i with the earlier holes tentatively filled. On failure, `conflict` is the set of
     * earlier holes whose fills the failure depends on: when it does not contain hole i - 1, other
     * fills of hole i - 1 cannot help and the caller backjumps.
     */
    const solve = async (i: number, tentative: Map<Hole, string>): Promise<Outcome> => {
      const h = task.holes[i];
      const last = i === n - 1;
      const earlier = () => new Set(Array.from({ length: i }, (_, j) => j));
      const ctx = new Map([...tentative].filter(([x]) => deps[i].has(task.holes.indexOf(x))));
      const ctxText = [...ctx].map(([x, c]) => `hole ${task.holes.indexOf(x) + 1} = ${c}`).join(", ");
      const label = n > 1 ? `hole ${i + 1}/${n} in ${task.name}${ctxText ? ` (with ${ctxText})` : ""}` : `hole in ${task.name}`;
      const key = [i, ...[...ctx].map(([x, c]) => `${task.holes.indexOf(x)}=${c}`)].join("\u0000");
      // an earlier hole's fill calls a helper whose proof rests on a sorry: no fill of this hole can
      // make the function proved with it (only another fill of that hole can)
      const tainted = taintedBy(tentative, sorryHelpers).map((x) => task.holes.indexOf(x));
      if (tainted.length) {
        console.log(`${label}: not searched: ${tainted.map((j) => `hole ${j + 1}'s fill (${tentative.get(task.holes[j])})`).join(", ")} calls ${[...sorryHelpers].filter((nm) => tainted.some((j) => callsAny(tentative.get(task.holes[j])!, new Set([nm])))).join(", ")}, whose proof rests on a sorry`);
        return { sol: null, conflict: new Set(tainted), failed: i, told: true };
      }
      let s = searches.get(key);
      const reused = !!s;
      if (!s) {
        if (Date.now() >= deadline) {
          halt = `the time limit for ${task.name} (${((deadline - t0All) / 1000).toFixed(0)}s for ${n} hole${n > 1 ? "s" : ""}) was reached`;
          console.log(`${label}: not searched: ${halt}`);
          return { sol: null, conflict: earlier() };
        }
        console.log(`${label}: ${showType(h.type)}   scope: ${h.scope.map((a) => a.code).join(", ")}`);
        const tps = tparamsOf.get(fd) ?? [];
        if (tps.length) {
          // (the body cannot tell which type it runs at: int and string stand for every type, or
          // for every type with equality — also under `K extends Color`)
          const shown = (p: TParam) => (p.fields ? `a record with ${p.fields.map((f) => f.name).join(", ")} and one more field` : `int or string${p.eq ? ", standing for every type with equality" : ", standing for every type"}`);
          console.log(`  tested with ${tps.map((p) => `${p.name} = ${shown(p)}`).join("; ")} (proved by Lean for every ${tps.map((p) => p.name).join(", ")})`);
        }
        s = searchOf(i, ctx);
        searches.set(key, s);
      } else {
        const indep = [...tentative.keys()].map((x) => task.holes.indexOf(x)).filter((j) => !deps[i].has(j));
        console.log(`${label}: same search as before${indep.length ? ` (a call reaching hole ${i + 1} never evaluates hole${indep.length > 1 ? "s" : ""} ${indep.map((j) => j + 1).join(", ")})` : ""}`);
      }
      // the candidates of this hole depend on the fills of deps[i] only
      const conflict = new Set(deps[i]);
      let examined = 0;
      // fills of this (non-final) hole tried with a search of the next hole
      let tried = 0;
      let leanChecks = 0;
      let stop = "";
      const rejected: string[] = [];
      const untranslatable: string[] = [];
      let sol: Map<Hole, string> | null = null;
      // candidates whose proof rests on a sorry of a helper they call (not proved; the next ones are tried)
      const viaSorry: string[] = [];
      // with several holes, a rejection may be the fault of an earlier fill: backtrack sooner
      const leanCap = n > 1 ? MAX_LEAN_CHECKS_JOINT : MAX_LEAN_CHECKS;
      for (let k = 0; !blocked && !halt; k++) {
        const sv = s.next(k);
        if (!sv) break;
        examined++;
        const ins = fillText(h, sv.code);
        // (what the tests said about it, for the messages)
        const passes = sv.untested ? `${ins} (untested)` : sv.cut ? `${ins} passes the tests that ran` : `${ins} passes the tests`;
        notes.set(h, { tested: s.tested, cand: passes });
        const after = `(${s.tested} candidate(s) tested in ${(s.searchMs / 1000).toFixed(1)}s)`;
        if (sv.cut) console.log(`  candidate passes the ${sv.valid} random tests that ran before its tests were cut off: ${ins}   ${after}`);
        else if (!sv.untested) console.log(`  candidate passes ${sv.valid} random tests: ${ins}   ${after}`);
        else console.log(`  untested candidate: ${ins}`);
        if (!last) {
          if (callsAny(ins, sorryHelpers)) {
            // (the function's proof would rest on that sorry whatever the later holes are filled with)
            console.log(`  ? not tried: ${ins} calls ${[...sorryHelpers].filter((nm) => callsAny(ins, new Set([nm]))).join(", ")}, whose proof rests on a sorry (see above)`);
            viaSorry.push(ins);
            if (viaSorry.length >= MAX_TENTATIVE + 5) {
              stop = `${viaSorry.length} fills of this hole that pass the tests call a helper whose proof rests on a sorry`;
              break;
            }
            continue;
          }
          tried++;
          console.log(`  … proof pending the other hole(s) of ${task.name}: searching hole ${i + 2} with this fill`);
          const r = await solve(i + 1, new Map([...tentative, [h, ins]]));
          if (r.sol) {
            sol = r.sol;
            break;
          }
          if (blocked || halt) break;
          if (!r.conflict.has(i)) {
            // the failure does not depend on this fill: no other fill of this hole can help (backjump
            // to the last hole it depends on)
            if (!r.told) {
              const to = Math.max(-1, ...r.conflict);
              const over = Array.from({ length: i - to }, (_, d) => to + d + 2);
              console.log(`  (hole ${(r.failed ?? i + 1) + 1} fails whatever the fill of hole${over.length > 1 ? "s" : ""} ${over.join(", ")}: no other fill of ${over.length > 1 ? "them" : "it"} is tried)`);
            }
            return { sol: null, conflict: r.conflict, failed: r.failed, told: true };
          }
          for (const c of r.conflict) if (c !== i) conflict.add(c);
          if (tried >= MAX_TENTATIVE) {
            stop = `${MAX_TENTATIVE} fills of this hole were tried with the next one`;
            break;
          }
          continue;
        }
        // Lean checks the whole function: its verdict depends on every fill
        for (const j of earlier()) conflict.add(j);
        if (callsAny(ins, sorryHelpers)) {
          console.log(`  ? not checked: ${ins} calls ${[...sorryHelpers].filter((nm) => callsAny(ins, new Set([nm]))).join(", ")}, whose proof rests on a sorry (see above)`);
          viaSorry.push(ins);
          if (examined >= leanCap + 5) {
            stop = `${examined} candidates passing the tests were not proved`;
            break;
          }
          continue;
        }
        const all = new Map([...accepted, ...tentative, [h, ins]]);
        const text = leanText(all);
        const cached = checks.has(text);
        if (!cached && leanRuns >= leanBudget) {
          halt = `the cap of ${leanBudget} Lean checks for ${task.name} was reached`;
          break;
        }
        const checked = check(text);
        const st = statusOf(checked, text, task, all);
        if (st.status === "untranslatable") {
          // (a synth limitation, not a verdict of Lean)
          console.log(`  ✗ ${ins}: does not translate: ${st.why}`);
          untranslatable.push(ins);
        } else {
          if (!cached) leanRuns++;
          leanChecks++;
          if (st.status === "proved") {
            const rel2 = st.relative.length ? ` (relative to ${st.relative.join(", ")}: @trusted or assumed, not proved)` : "";
            console.log(n > 1 ? `  ✔ proved by Lean: ${task.name} with ${[...tentative.values(), ins].join(" / ")}${rel2}` : `  ✔ proved by Lean: ${ins}${rel2}`);
            provedRelative = st.relative;
            sol = all;
            break;
          }
          if (st.status === "rejected") {
            console.log(`  ✗ Lean rejects ${ins}: ${st.why}`);
            rejected.push(ins);
          } else {
            // blocked / pending because of a helper that this function's fills call (whose proof
            // rests on a sorry): only the fills calling it are affected
            const own = sorryCallees(checked, [...tentative.values(), ins]);
            for (const nm of own) sorryHelpers.add(nm);
            const theirs = taintedBy(tentative, new Set(own)).map((x) => task.holes.indexOf(x));
            if (theirs.length) {
              // an earlier hole's fill calls it: so would every candidate of this hole with that fill
              const which = theirs.map((j) => `hole ${j + 1} (${tentative.get(task.holes[j])})`).join(", ");
              console.log(`  ? not proved: ${passes}, but ${st.why}: the fill of ${which} calls ${own.filter((nm) => theirs.some((j) => callsAny(tentative.get(task.holes[j])!, new Set([nm])))).join(", ")}, whose proof rests on a sorry (a failed obligation or a hole); fills of ${theirs.length > 1 ? "those holes" : `hole ${theirs[0] + 1}`} that do not call it are tried next`);
              notes.set(h, { ...notes.get(h), tested: s.tested, last: `the fill of ${which} calls a helper whose proof rests on a sorry` });
              return { sol: null, conflict: new Set(theirs), failed: i, told: true };
            }
            if (own.length) {
              console.log(`  ? not proved: ${passes}, but ${st.why}: it calls ${own.join(", ")}, whose proof rests on a sorry (a failed obligation or a hole); candidates that do not call ${own.length > 1 ? "them" : "it"} are tried next`);
              viaSorry.push(ins);
            } else {
              // no candidate of this function can be checked now
              console.log(`  ? not proved: ${passes}, but ${st.why}`);
              blocked = st.why;
              break;
            }
          }
        }
        if (leanChecks >= leanCap || examined >= leanCap + 5) {
          stop = `${examined} candidates passing the tests were not proved`;
          break;
        }
      }
      if (sol) return { sol, conflict };
      const viaSorryNote = viaSorry.length ? `the candidate(s) that pass the tests call ${[...sorryHelpers].join(", ")}, whose proof rests on a sorry` : "";
      notes.set(h, { ...notes.get(h), tested: s.tested, last: viaSorryNote || stop || s.stop });
      if (blocked || halt) return { sol: null, conflict, failed: i };
      const untestedNote = s.deferred ? ` (${s.deferred} could not be tested, e.g. ${s.untestableSome})` : "";
      const what = s.untestable ?? (s.passed ? `${s.passed} candidate(s) passed the tests, none was proved${untestedNote}` : `no candidate passed the tests${untestedNote}`);
      if (!reused) {
        console.log(`  ${s.tested} candidates tested in ${(s.searchMs / 1000).toFixed(1)}s, up to size ${s.sizeReached}; stopped: ${stop || s.stop || "search exhausted"}`);
        const top = [...s.fails.entries()].sort((a, b) => b[1].n - a[1].n)[0];
        console.log(`  no verified solution for ${label}: ${what}`);
        if (top && !s.passed) console.log(`  most common failure (${top[1].n}×): ${top[1].example}`);
      } else console.log(`  no verified solution for ${label}: ${what}`);
      // (candidates that do not translate never reached Lean: they are not Lean rejections)
      const eg = (xs: string[]) => xs.slice(0, 2).join("; ") + (xs.length > 2 ? `; … ${xs.length - 2} more` : "");
      if (rejected.length && s.untestable) console.log("  the inputs cannot test this hole and Lean rejects the smallest candidates: write this one by hand");
      else if (rejected.length) console.log("  the random tests accept candidates that Lean rejects: write this one by hand");
      else if (untranslatable.length) console.log(`  the candidate(s) that pass the tests do not translate (${eg(untranslatable)}): a synth limitation, write this one by hand`);
      else if (viaSorry.length) console.log(`  the candidate(s) that pass the tests (${eg(viaSorry)}) call ${[...sorryHelpers].join(", ")}, whose proof rests on a sorry: fix ${sorryHelpers.size > 1 ? "them" : "it"} first, or write this one by hand`);
      // (Maps and Sets: the grammar only grows them, so a fill that deletes is never found)
      else if (last || !s.passed) console.log(`  write this one by hand (synth builds straight-line expressions; guarded updates need an \`if\`${s.collections ? "; it only adds to a Map or Set, by new Map(m).set(k, v) or new Set(s).add(x): deleting is not in its grammar" : ""}), or check that the spec is satisfiable`);
      return { sol: null, conflict, failed: i };
    };

    const { sol: solution } = await solve(0, new Map());
    if (solution) {
      for (const h of task.holes) {
        accepted.set(h, solution.get(h)!);
        record(h, solution.get(h)!, notes.get(h)?.tested ?? 0, provedStatus(provedRelative), provedRelative.length ? relNote(provedRelative) : undefined, provedRelative);
      }
      acceptedTasks.push(task);
    } else {
      for (const h of task.holes) {
        const nt = notes.get(h);
        record(h, null, nt?.tested ?? 0, "not-proved", blocked ? `${nt?.cand ? `${nt.cand}, but ` : ""}${blocked}` : (halt ?? nt?.last));
      }
      if (halt) console.log(`  stopped: ${halt}`);
      if (n > 1) console.log(`  (no hole of ${task.name} is filled: its holes are only proved together)`);
    }
  }

  // ---- result: the written text is exactly the one Lean checked ----
  if (accepted.size) {
    const final = leanText(accepted);
    // the last check of each accepted function may predate later fills: re-check the final text once
    const c = check(final);
    const finalSt = acceptedTasks.map((t) => [t, statusOf(c, final, t, accepted)] as const);
    const bad = finalSt.filter(([, s]) => s.status !== "proved");
    if (bad.length) {
      for (const [t, s] of bad) console.log(`✗ ${t.name} is no longer proved in the final program (${s.status}: ${"why" in s ? s.why : ""}): nothing written`);
      for (const r of results) if (bad.some(([t]) => t.name === r.fn)) Object.assign(r, { proved: false, status: "not-proved", relative_to: undefined });
    } else {
      // what the written program's proofs assume
      for (const [t, s] of finalSt) {
        if (s.status !== "proved") continue;
        for (const r of results) {
          if (r.fn !== t.name || !r.proved) continue;
          r.status = provedStatus(s.relative);
          if (s.relative.length) Object.assign(r, { relative_to: s.relative, note: relNote(s.relative) });
          else delete r.relative_to;
        }
      }
      if (opts.write) {
        if (fs.readFileSync(target, "utf8") !== raw) console.log(`✗ ${rel} changed while synth was running: not written`);
        else {
          fs.writeFileSync(target, bom + final);
          console.log(`wrote ${rel}`);
        }
      } else console.log(`(${rel} not modified: rerun with --write to keep the proved fill(s))`);
    }
  }
  if (opts.json) console.log(JSON.stringify(results, null, 2));
  return results;
}
