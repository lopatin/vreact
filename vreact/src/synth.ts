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
 *      variant literals, ±1 arithmetic, comparisons, calls of total helpers.
 *   3. Test each candidate by *running the real transpiled JavaScript* on random
 *      inputs: the function's own `requires` filters inputs, its own `ensures`
 *      must hold on the result (counterexample-driven pruning). Inputs that reach
 *      another, still unfilled hole are skipped.
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
 * The source file is never modified while searching: candidates are checked
 * from memory (`Config.overrides`). With `--write`, the proved fills are written
 * once at the end.
 */
import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { pathToFileURL } from "node:url";
import { loadConfig } from "./cli.ts";
import { translate, overrideHost, moduleNs, isComponentDecl, type Config, type TranslateResult } from "./module.ts";
import { runLake, findMarkers, judge, type Verdict } from "./lean.ts";
import { Program, ModCtx, refSymbol, type HoleEnv } from "./ctx.ts";
import { type VType, type Field, T, typeOfNode, typeOfDecl, showType, sharedFields, registerTypeParams, type TParam, type TypeRegistry, sameType, isEqType, substType, mentionsTVar } from "./types.ts";
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
const STD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);
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
  return [K.Identifier, K.PropertyAccessExpression, K.ElementAccessExpression, K.CallExpression, K.NumericLiteral, K.StringLiteral, K.NoSubstitutionTemplateLiteral, K.ArrayLiteralExpression, K.TrueKeyword, K.FalseKeyword, K.NullKeyword, K.ParenthesizedExpression].includes(e.kind);
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

/** Drop `hole` from the vreact/spec import when the text no longer uses it (noUnusedLocals). */
function dropUnusedHoleImport(text: string, fileName: string): string {
  const { sf, checker } = fileChecker(fileName, text);
  for (const st of sf.statements) {
    if (!ts.isImportDeclaration(st) || !ts.isStringLiteral(st.moduleSpecifier) || !SPEC_RE.test(st.moduleSpecifier.text)) continue;
    const nb = st.importClause?.namedBindings;
    if (!nb || !ts.isNamedImports(nb) || st.importClause?.isTypeOnly) continue;
    const els = nb.elements;
    const i = els.findIndex((e) => (e.propertyName ?? e.name).text === "hole" && !e.isTypeOnly);
    if (i < 0) continue;
    const local = els[i].name.text;
    // only references to the imported binding count: not a field or property spelled `hole`,
    // nor a local (parameter, destructured name) that shadows it
    const imported = checker.getSymbolAtLocation(els[i].name);
    let used = false;
    const visit = (n: ts.Node) => {
      if (used || n === st) return;
      if (ts.isIdentifier(n) && n.text === local && !isPropertyName(n)) {
        const p = n.parent;
        const s = ts.isShorthandPropertyAssignment(p) && p.name === n ? checker.getShorthandAssignmentValueSymbol(p) : checker.getSymbolAtLocation(n);
        // (no symbol at all: keep the import, to be safe)
        if (!imported || !s || s === imported) used = true;
      }
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(sf, visit);
    if (used) return text;
    if (els.length === 1 && !st.importClause!.name) {
      // the whole import goes (with its line break)
      let end = st.getEnd();
      if (text[end] === "\r") end++;
      if (text[end] === "\n") end++;
      return text.slice(0, st.getStart(sf)) + text.slice(end);
    }
    const [a, b] = i < els.length - 1 ? [els[i].getStart(sf), els[i + 1].getStart(sf)] : [els[i - 1].getEnd(), els[i].getEnd()];
    return text.slice(0, a) + text.slice(b);
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
      const p = `${name}.${f.name}`;
      const ft = narrowT(p, f.type);
      scope.push({ code: p, type: ft, size: 1 });
      if (ft.k === "rec" || (ft.k === "union" && narrowed.get(p)?.variants)) {
        for (const g of fieldsOf(ft, narrowed.get(p)?.variants)) scope.push({ code: `${p}.${g.name}`, type: narrowT(`${p}.${g.name}`, g.type), size: 2 });
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
  }
  terms(t: VType, size: number): Atom[] {
    const k = key(t);
    let tab = this.bySize.get(k);
    if (!tab) {
      tab = [];
      this.bySize.set(k, tab);
    }
    if (tab[size] === undefined) {
      const built = this.build(t, size);
      // bound the search space: keep the first MAX_TERMS terms of each type and size
      if (built.length > MAX_TERMS) this.capped = true;
      tab[size] = built.length > MAX_TERMS ? built.slice(0, MAX_TERMS) : built;
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
      default:
        return [];
    }
  }
  build(t: VType, size: number): Atom[] {
    const reg = this.prog.reg;
    const out: Atom[] = [];
    const push = (code: string) => out.push({ code, type: t, size });
    const same = (a: VType) => key(a) === key(t);
    if (size === 1) {
      for (const a of this.scope) if (a.size === 1 && same(a.type)) push(a.code);
      for (const l of this.literals(t)) push(l);
      return out;
    }
    if (size === 2) for (const a of this.scope) if (a.size === 2 && same(a.type)) push(a.code);
    // calls of helper functions of the module: f(a1, …, an)
    for (const h of this.helpers) {
      if (!same(h.ret) || h.params.length === 0 || size - 1 < h.params.length) continue;
      const sp = (n: number, parts: number): number[][] => {
        if (parts === 1) return n >= 1 ? [[n]] : [];
        const r: number[][] = [];
        for (let i = 1; i <= n - parts + 1; i++) for (const rest of sp(n - i, parts - 1)) r.push([i, ...rest]);
        return r;
      };
      for (const split of sp(size - 1, h.params.length)) {
        let partial: string[][] = [[]];
        for (let i = 0; i < h.params.length; i++) {
          const opts = this.terms(h.params[i], split[i]).map((a) => a.code);
          const next: string[][] = [];
          for (const p of partial) for (const o of opts) next.push([...p, o]);
          partial = next;
          if (partial.length > 2000) break;
        }
        for (const args of partial) if (args.length === h.params.length) push(`${h.name}(${args.join(", ")})`);
      }
    }
    const splits = (n: number, parts: number): number[][] => {
      if (parts === 1) return n >= 1 ? [[n]] : [];
      const r: number[][] = [];
      for (let i = 1; i <= n - parts + 1; i++) for (const rest of splits(n - i, parts - 1)) r.push([i, ...rest]);
      return r;
    };
    switch (t.k) {
      case "int": {
        for (const a of this.terms(T.int, size - 1)) {
          push(`${a.code} + 1`);
          push(`${a.code} - 1`);
        }
        for (const [i, j] of splits(size - 1, 2)) for (const a of this.terms(T.int, i)) for (const b of this.terms(T.int, j)) if (a.code < b.code) push(`${a.code} + ${b.code}`);
        for (const [tk, tt] of this.types) if (tt.k === "arr") for (const a of this.terms(tt, size - 1)) if (!a.code.includes("=>")) push(`${a.code}.length`);
        break;
      }
      case "bool": {
        for (const a of this.terms(T.bool, size - 1)) push(`!${wrap(a.code)}`);
        for (const [i, j] of splits(size - 1, 2)) {
          // (values of a type parameter: only under an equality constraint)
          const eqTVars = [...this.types.values()].filter((x) => x.k === "tvar" && x.eq);
          for (const pt of [T.int, T.str, ...eqTVars]) {
            for (const a of this.terms(pt, i)) for (const b of this.terms(pt, j)) {
              if (a.code === b.code) continue;
              push(`${wrap(a.code)} === ${wrap(b.code)}`);
              if (pt.k === "int") push(`${wrap(a.code)} < ${wrap(b.code)}`);
            }
          }
        }
        break;
      }
      case "str": {
        for (const a of this.terms(T.str, size - 1)) if (!a.code.endsWith(".trim()")) push(`${wrap(a.code)}.trim()`);
        break;
      }
      case "opt": {
        for (const a of this.terms(t.elem, size - 1)) push(a.code);
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
                push(`{ ...${v.code}, ${f.name}: ${e.code} }`);
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
                push(`{ ...${v.code}, ${f.name}: ${e1.code}, ${g.name}: ${e2.code} }`);
              }
            }
          }
        }
        // full literal (fields from small terms)
        if (fields.length && size - 1 >= fields.length) {
          for (const sp of splits(size - 1, fields.length)) {
            if (sp.some((x) => x > 3)) continue;
            let partial: string[][] = [[]];
            for (let fi = 0; fi < fields.length; fi++) {
              const opts = this.terms(fields[fi].type, sp[fi]).map((e) => `${fields[fi].name}: ${e.code}`);
              const next: string[][] = [];
              for (const p of partial) for (const o of opts) next.push([...p, o]);
              partial = next;
              if (partial.length > 4000) break;
            }
            for (const p of partial) if (p.length === fields.length) push(`{ ${p.join(", ")} }`);
          }
        }
        break;
      }
      case "union": {
        const u = reg.union(t);
        for (const v of u.variants) {
          if (v.fields.length === 0) {
            if (size === 2) push(`{ ${u.tag}: ${JSON.stringify(v.lit)} }`);
            continue;
          }
          for (const sp of splits(size - 1, v.fields.length)) {
            let partial: string[][] = [[]];
            for (let fi = 0; fi < v.fields.length; fi++) {
              const opts = this.terms(v.fields[fi].type, sp[fi]).map((e) => `${v.fields[fi].name}: ${e.code}`);
              const next: string[][] = [];
              for (const p of partial) for (const o of opts) next.push([...p, o]);
              partial = next;
            }
            for (const p of partial) push(`{ ${u.tag}: ${JSON.stringify(v.lit)}, ${p.join(", ")} }`);
          }
        }
        break;
      }
      case "arr": {
        const E = t.elem;
        // [...xs, e]
        for (const [i, j] of splits(size - 1, 2)) for (const xs of this.terms(t, i)) for (const e of this.terms(E, j)) push(`[...${xs.code}, ${e.code}]`);
        // [...xs, ...ys]
        for (const [i, j] of splits(size - 1, 2)) {
          for (const xs of this.terms(t, i)) for (const ys of this.terms(t, j)) {
            if (xs.code === "[]" || ys.code === "[]") continue;
            push(`[...${xs.code}, ...${ys.code}]`);
          }
        }
        // [e]
        for (const e of this.terms(E, size - 1)) push(`[${e.code}]`);
        // (the fields of a record element, or the constrained fields of a type parameter's)
        const elemFields = E.k === "rec" ? reg.rec(E) : E.k === "tvar" ? (E.fields ?? []) : [];
        if (elemFields.length && this.lambdaDepth === 0) {
          const fields = elemFields;
          const keys = fields.filter((f) => ["int", "str", "enum"].includes(f.type.k));
          // xs.filter((x) => x.k !== v)
          for (const [i, j] of splits(size - 2, 2)) {
            for (const xs of this.terms(t, i)) {
              if (xs.code.includes("=>")) continue;
              for (const k of keys) for (const v of this.terms(k.type, j)) {
                if (/\bx\b/.test(v.code)) continue;
                push(`${wrap(xs.code)}.filter((x) => x.${k.name} !== ${v.code})`);
                push(`${wrap(xs.code)}.filter((x) => x.${k.name} === ${v.code})`);
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
                    push(`${wrap(xs.code)}.map((x) => (x.${k.name} === ${v.code} ? { ...x, ${f.name}: ${e} } : x))`);
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
    return out;
  }
  /** terms of type `ft` over the scope extended with the lambda variable `x : E` */
  inner(E: VType, ft: VType, size: number): string[] {
    const reg = this.prog.reg;
    const xs: Atom[] = [{ code: "x", type: E, size: 1 }];
    if (E.k === "rec") for (const f of reg.rec(E)) xs.push({ code: `x.${f.name}`, type: f.type, size: 1 });
    if (E.k === "tvar") for (const f of E.fields ?? []) xs.push({ code: `x.${f.name}`, type: f.type, size: 1 });
    const sub = new Enumerator(this.prog, [...this.scope.filter((a) => !a.code.startsWith("x")), ...xs], ft, size);
    sub.lambdaDepth = 1;
    const r = sub.terms(ft, size).map((a) => a.code).filter((c) => /\bx\b/.test(c) || size === 1);
    if (sub.capped) this.capped = true;
    return r;
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

function rnd(n: number) {
  return Math.floor(Math.random() * n);
}
const pick = <A>(xs: A[]): A => xs[rnd(xs.length)];

/**
 * The instantiation of a generic function's type parameters for one test input (by id): `int`
 * or `string` for an unconstrained or equality-constrained parameter, a witness record (the
 * constrained fields and one more) for a field-constrained one.  The function is compiled once
 * (types are erased); Lean proves the fill once for every instantiation.
 */
type Inst = Map<number, VType | "witness">;

function chooseInst(tparams: readonly TParam[]): Inst {
  return new Map(tparams.map((p) => [p.id, p.fields ? "witness" : Math.random() < 0.5 ? T.int : T.str]));
}

function gen(t: VType, prog: Program, pools: Pools, depth = 0, inst?: Inst): unknown {
  const reg = prog.reg;
  switch (t.k) {
    case "tvar": {
      const c = inst?.get(t.id);
      // (never a silent `undefined`: every value of a type parameter comes from an instantiation)
      if (!c) throw new Error(`internal: no test instantiation of the type parameter ${t.name}`);
      if (c !== "witness") return gen(c, prog, pools, depth, inst);
      const o: Record<string, unknown> = {};
      for (const f of t.fields ?? []) o[f.name] = gen(f.type, prog, pools, depth + 1, inst);
      // (a field the constraint does not name: a fill that rebuilds the value loses it)
      if (!("witness$" in o)) o.witness$ = pick(BASE_STRS);
      return o;
    }
    case "int":
      return pools.ints.length && Math.random() < 0.4 ? pick(pools.ints) : pick(BASE_INTS);
    case "num":
      return Math.random() * 10 - 2;
    case "bool":
      return Math.random() < 0.5;
    case "str":
      return pools.strs.length && Math.random() < 0.3 ? pick(pools.strs) : pick(BASE_STRS);
    case "enum": {
      const lits = reg.enumLits(t);
      return lits[rnd(lits.length)];
    }
    case "opt": {
      if (Math.random() >= 0.3) return gen(t.elem, prog, pools, depth, inst);
      const a = (t as OptT).absent ?? "null";
      return a === "undefined" || (a === "both" && Math.random() < 0.5) ? undefined : null;
    }
    case "tuple":
      return t.elems.map((e) => gen(e, prog, pools, depth, inst));
    case "rec": {
      const o: Record<string, unknown> = {};
      for (const f of reg.rec(t)) o[f.name] = gen(f.type, prog, pools, depth + 1, inst);
      return o;
    }
    case "union": {
      const u = reg.union(t);
      const v = u.variants[rnd(u.variants.length)];
      const o: Record<string, unknown> = { [u.tag]: v.lit };
      for (const f of v.fields) o[f.name] = gen(f.type, prog, pools, depth + 1, inst);
      return o;
    }
    case "arr": {
      const n = depth > 2 ? 0 : rnd(4);
      const xs = Array.from({ length: n }, () => gen(t.elem, prog, pools, depth + 1, inst));
      // favour distinct ids (common invariant)
      if ((t.elem.k === "rec" || (t.elem.k === "tvar" && t.elem.fields)) && xs.length) {
        const ids = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6].sort(() => Math.random() - 0.5);
        xs.forEach((x, i) => {
          if (x && typeof x === "object" && "id" in (x as object) && Math.random() < 0.9) (x as Record<string, unknown>).id = ids[i];
        });
      }
      return xs;
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

/* ───────────────────────── running candidates ───────────────────────── */

/**
 * Evaluates project modules as CommonJS function bodies (no ES module cache:
 * each candidate's module is garbage once its tests ran). Dependencies of the
 * target file are loaded once; `vreact/spec` is the real runtime module.
 */
class Sandbox {
  private cache = new Map<string, Record<string, unknown>>();
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
          this.cache.set(f, m);
          this.evalModule(f, fs.readFileSync(f, "utf8").replace(/^\uFEFF/, ""), "", m);
        }
        return m;
      }
      if (!f || !/\.(c?js|json)$/.test(f)) return {}; // stylesheets, images: irrelevant to model functions
      return createRequire(from)(f);
    }
    return createRequire(from)(spec);
  }
  /** Run `text` (TS source of `file`) as a CommonJS module; `epilogue` is appended JS. */
  evalModule(file: string, text: string, epilogue = "", exports: Record<string, unknown> = {}): Record<string, unknown> {
    const js = ts.transpileModule(text, {
      compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, jsx: ts.JsxEmit.ReactJSX, esModuleInterop: true, verbatimModuleSyntax: false },
      fileName: file,
    }).outputText;
    const module = { exports };
    const body = new Function("exports", "require", "module", "__filename", "__dirname", js + "\n" + epilogue);
    body(module.exports, (s: string) => this.require(file, s), module, file, path.dirname(file));
    return module.exports;
  }
}

interface RunResult {
  ok: boolean;
  valid: number;
  why?: string;
  /** no generated input exercises the hole (independent of the candidate) */
  untestable?: string;
  /** failure category for the summary */
  cat?: string;
}

interface Runner {
  run(candidate: string): RunResult;
}

const OWN_ENSURES = "__vreactOwnEnsures__";
const OWN_REQUIRES = "__vreactOwnRequires__";
const TARGET = "__vreactSynthTarget__";
const OTHER_HOLE = { other: "hole" };
const OWN_PRE = { own: "precondition" };
/** what vreact/spec's hole() throws outside test mode (the contracts are evaluated outside it) */
const isUnfilledHoleError = (e: unknown) => e instanceof Error && e.message.startsWith("vreact: unfilled hole()");

function makeRunner(sb: Sandbox, target: string, fname: string, paramTypes: VType[], prog: Program, pools: Pools, textFor: (cand: string) => string, tparams: readonly TParam[] = []): Runner {
  // fixed sample set (re-used across candidates; counterexamples are moved to the front); the
  // parameters of one input share one instantiation of the type parameters
  const samples: unknown[][] = Array.from({ length: 400 }, () => {
    const inst = chooseInst(tparams);
    return paramTypes.map((t) => gen(t, prog, pools, 0, inst));
  });
  const g = globalThis as Record<string, unknown>;
  return {
    run(candidate) {
      let f: (...a: unknown[]) => unknown;
      try {
        const exp = sb.evalModule(target, textFor(candidate), `module.exports.${TARGET} = ${fname};`);
        f = exp[TARGET] as typeof f;
      } catch (e) {
        return { ok: false, valid: 0, why: "does not load: " + (e as Error).message, cat: "does not load" };
      }
      let valid = 0;
      let pre = 0;
      let other = 0;
      let contract = 0;
      for (let i = 0; i < samples.length; i++) {
        const args = structuredClone(samples[i]);
        const own: ((r: unknown) => boolean)[] = [];
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
        let r: unknown;
        try {
          r = f(...args);
        } catch (e) {
          if (e === OWN_PRE) {
            pre++;
            continue;
          }
          if (e === OTHER_HOLE) {
            other++;
            continue;
          }
          samples.unshift(samples.splice(i, 1)[0]);
          if ((e as Error)?.constructor?.name === "PreconditionFailed") return { ok: false, valid, why: `a call violates a precondition on ${JSON.stringify(args)}`, cat: "a call violates a precondition" };
          return { ok: false, valid, why: `throws on ${JSON.stringify(args)}: ${(e as Error)?.message}`, cat: "throws" };
        } finally {
          g.__VREACT_TEST__ = undefined;
          g[OWN_ENSURES] = undefined;
          g[OWN_REQUIRES] = undefined;
        }
        let verdict: "pass" | "fail" | "skip" = "pass";
        for (const p of own) {
          try {
            if (!p(r)) verdict = "fail";
          } catch (e) {
            // the contract calls a function that still has a hole: this input cannot judge the candidate
            verdict = isUnfilledHoleError(e) ? "skip" : "fail";
          }
          if (verdict !== "pass") break;
        }
        if (verdict === "skip") {
          contract++;
          continue;
        }
        valid++;
        if (verdict === "fail") {
          samples.unshift(samples.splice(i, 1)[0]); // counterexample first next time
          return { ok: false, valid, why: `postcondition fails on ${JSON.stringify(args)} ↦ ${JSON.stringify(r)}`, cat: "postcondition fails" };
        }
      }
      if (valid > 0) return { ok: true, valid };
      if (contract > 0) {
        // (not "postcondition fails": the contract cannot be evaluated, e.g. it calls a @trusted stub whose body is a hole)
        const why = `no generated input can test this hole: the contract of ${fname} runs into a hole (unfinished code it calls) on every input that reaches it (${contract} of ${samples.length})`;
        return { ok: false, valid: 0, why, untestable: why };
      }
      const why =
        pre === samples.length ? `no generated input satisfies the precondition of ${fname} (is it satisfiable?)`
        : other + pre === samples.length ? `no generated input can test this hole (${other} of ${samples.length} reach another unfilled hole)`
        : "no generated input exercises this hole";
      return { ok: false, valid: 0, why, untestable: why };
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
  untestable: string | null;
  searchMs: number;
  fails: Map<string, { n: number; example: string }>;
}

function newSearch(h: Hole, en: Enumerator, runner: Runner, maxSize: number, limitMs: number): Search {
  const S: Search = { next: () => null, tested: 0, passed: 0, sizeReached: 0, stop: "", untestable: null, searchMs: 0, fails: new Map() };
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
  function* run(): Generator<Survivor> {
    // search time excludes the Lean checks done while the generator is suspended
    let resume = Date.now();
    const pause = () => {
      S.searchMs += Date.now() - resume;
      resume = -1;
    };
    try {
      for (let size = 1; size <= maxSize; size++) {
        S.sizeReached = size;
        for (const c of en.build(h.type, size)) {
          if (S.searchMs + (Date.now() - resume) > limitMs) {
            S.stop = `the ${(limitMs / 1000).toFixed(0)}s time limit was reached at size ${size}`;
            return;
          }
          if (S.tested >= MAX_CANDIDATES) {
            S.stop = `the cap of ${MAX_CANDIDATES} candidates was reached at size ${size}`;
            return;
          }
          if (seenText.has(c.code)) continue;
          seenText.add(c.code);
          if (S.untestable) {
            // the inputs cannot exercise this hole: the smallest candidates go to Lean untested
            if (untested++ >= MAX_UNTESTED) {
              S.stop = `${MAX_UNTESTED} untested candidates were tried`;
              return;
            }
            if (!fresh(c.code)) continue;
            pause();
            yield { code: c.code, valid: 0, untested: true };
            resume = Date.now();
            continue;
          }
          S.tested++;
          const r = runner.run(c.code);
          if (process.env.VREACT_SYNTH_DEBUG && S.tested <= 12) console.log(`    [${r.ok ? "pass" : "fail"}] ${c.code}  ${r.why ?? ""}`);
          if (r.untestable) {
            S.untestable = r.untestable;
            console.log(`  ${r.untestable}: the smallest candidates are checked by Lean only`);
            untested++;
            fresh(c.code);
            pause();
            yield { code: c.code, valid: 0, untested: true };
            resume = Date.now();
            continue;
          }
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
      S.stop = `all candidates up to size ${maxSize} were tried` + (en.capped ? ` (sub-expression lists were capped at ${MAX_TERMS} per type and size, so some larger candidates were never built)` : "");
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

export async function synthCommand(root: string, files: string[], opts: { write?: boolean; json?: boolean; maxSize?: number }): Promise<SynthResult[]> {
  if (!files.length) throw new Error("usage: vreact synth <file.tsx> [--write]");
  const cfg = loadConfig(root);
  const maxSize = opts.maxSize ?? 9;
  // the file as the program knows it (same spelling as cfg.files: case-insensitive file systems, symlinks)
  const typed = path.resolve(root, files[0]);
  const real = (f: string) => fs.realpathSync.native(f);
  const target = fs.existsSync(typed) ? cfg.files.find((f) => fs.existsSync(f) && real(f) === real(typed)) : undefined;
  if (!target) {
    console.log(fs.existsSync(typed) ? `✗ ${files[0]} is not one of the project's VTS files (see "src"/"include"/"exclude" in vreact.json)` : `✗ ${files[0]}: no such file`);
    process.exitCode = 1;
    return [];
  }
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
    let task = tasks.find((t) => t.fn === fd);
    if (!task) tasks.push((task = { fn: fd, name, holes: [], ensures: 0 }));
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
  for (const t of tasks) visitTask(t, new Set());

  const sb = holeCalls.length ? await Sandbox.create(target) : null;
  const accepted = new Map<Hole, string>(); // proved fills (text inserted at the hole)
  const acceptedTasks: Task[] = [];
  const editsOf = (fills: Map<Hole, string>): Edit[] => [...fills].map(([h, text]) => ({ at: h.span, text }));
  const leanText = (fills: Map<Hole, string>) => dropUnusedHoleImport(applyEdits(base, editsOf(fills)), target);
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
  const provedStatus = (relative: string[]) => (relative.length ? "proved-relative" : "proved");
  const relNote = (relative: string[]) => `proved assuming ${relative.join(", ")} (@trusted contracts, assume(…) facts or axioms of user proofs, not proved)`;

  for (const task of ordered) {
    const fd = task.fn;
    const n = task.holes.length;
    const holesLabel = n > 1 ? `${n} holes in ${task.name}` : `hole in ${task.name}`;
    const record = (h: Hole, solution: string | null, tested: number, status: string, note?: string, relative?: string[]) => {
      results.push({ fn: task.name, hole: showType(h.type), solution, tested, proved: status === "proved" || status === "proved-relative", status, ...(relative?.length ? { relative_to: relative } : {}), note });
    };
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
    const deadline = t0All + TIME_LIMIT_MS * (n + 1);
    const leanBudget = MAX_LEAN_CHECKS * n;
    let leanRuns = 0;
    let blocked: string | null = null; // no fill of this function can be checked now
    let halt: string | null = null; // this function's time or Lean-check budget is spent
    let provedRelative: string[] = [];
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
      const runner = makeRunner(sb!, target, task.name, pTypes as VType[], prog, pools, (cand) => applyEdits(base, [...editsOf(new Map([...accepted, ...ctx, [h, fillText(h, cand)]])), ...ownContract]), tparamsOf.get(fd) ?? []);
      return newSearch(h, en, runner, maxSize, Math.min(TIME_LIMIT_MS, Math.max(5000, deadline - Date.now())));
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
      let leanChecks = 0;
      let stop = "";
      const rejected: string[] = [];
      const untranslatable: string[] = [];
      let sol: Map<Hole, string> | null = null;
      // with several holes, a rejection may be the fault of an earlier fill: backtrack sooner
      const leanCap = n > 1 ? MAX_LEAN_CHECKS_JOINT : MAX_LEAN_CHECKS;
      for (let k = 0; !blocked && !halt; k++) {
        const sv = s.next(k);
        if (!sv) break;
        examined++;
        const ins = fillText(h, sv.code);
        notes.set(h, { tested: s.tested, cand: ins });
        const after = `(${s.tested} candidate(s) tested in ${(s.searchMs / 1000).toFixed(1)}s)`;
        if (!sv.untested) console.log(`  candidate passes ${sv.valid} random tests: ${ins}   ${after}`);
        else console.log(`  untested candidate: ${ins}`);
        if (!last) {
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
          if (examined >= MAX_TENTATIVE) {
            stop = `${MAX_TENTATIVE} fills of this hole were tried with the next one`;
            break;
          }
          continue;
        }
        // Lean checks the whole function: its verdict depends on every fill
        for (const j of earlier()) conflict.add(j);
        const all = new Map([...accepted, ...tentative, [h, ins]]);
        const text = leanText(all);
        const cached = checks.has(text);
        if (!cached && leanRuns >= leanBudget) {
          halt = `the cap of ${leanBudget} Lean checks for ${task.name} was reached`;
          break;
        }
        const st = statusOf(check(text), text, task, all);
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
            // blocked / pending: no candidate of this function can be checked now
            console.log(`  ? not proved: ${ins} passes the tests, but ${st.why}`);
            blocked = st.why;
            break;
          }
        }
        if (leanChecks >= leanCap || examined >= leanCap + 5) {
          stop = `${examined} candidates passing the tests were not proved`;
          break;
        }
      }
      if (sol) return { sol, conflict };
      notes.set(h, { ...notes.get(h), tested: s.tested, last: stop || s.stop });
      if (blocked || halt) return { sol: null, conflict, failed: i };
      const what = s.untestable ?? (s.passed ? `${s.passed} candidate(s) passed the tests, none was proved` : "no candidate passed the tests");
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
      else if (last || !s.passed) console.log("  write this one by hand (synth builds straight-line expressions; guarded updates need an `if`), or check that the spec is satisfiable");
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
        record(h, null, nt?.tested ?? 0, "not-proved", blocked ? `${nt?.cand ? `${nt.cand} passes the tests, but ` : ""}${blocked}` : (halt ?? nt?.last));
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
