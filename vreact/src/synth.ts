/**
 * vreact synth — fill `hole<T>()` placeholders against the function's contract.
 *
 *   1. Scope: parameters of the enclosing function, refined by the narrowing in
 *      effect at the hole (switch/if on a discriminant, null tests, early returns),
 *      mirroring the translator's narrowing.
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
 *      checked once the function is complete).
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
import { translate, overrideHost, type Config, type TranslateResult } from "./module.ts";
import { runLake, findMarkers, judge, summarizeLeanError, type Verdict } from "./lean.ts";
import { Program, ModCtx } from "./ctx.ts";
import { type VType, type Field, T, typeOfNode, typeOfDecl, showType, sharedFields } from "./types.ts";
import { specFn } from "./translate.ts";
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
/** Lean checks per hole before giving up on further survivors */
const MAX_LEAN_CHECKS = 5;
/** Lean checks of the last hole of a function with several holes, per fill of the earlier ones */
const MAX_LEAN_CHECKS_JOINT = 2;
/** survivors of a non-final hole explored (each one with a search for the next hole) */
const MAX_TENTATIVE = 3;
/** candidates sent to Lean untested when no generated input exercises the hole */
const MAX_UNTESTED = 3;
const STD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);
const SPEC_RE = /vreact[\\/](spec|lib)|vreact-spec/;

/** Same test as the translator (module.ts isComponentDecl). */
function isComponent(fn: ts.FunctionDeclaration): boolean {
  if (!/^[A-Z]/.test(fn.name?.text ?? "")) return false;
  if (fn.type && /JSX\.Element|ReactNode|ReactElement/.test(fn.type.getText())) return true;
  let jsx = false;
  const visit = (n: ts.Node) => {
    if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n)) jsx = true;
    if (!jsx) ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return jsx;
}

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

/** Drop `hole` from the vreact/spec import when the text no longer uses it (noUnusedLocals). */
function dropUnusedHoleImport(text: string, fileName: string): string {
  const sf = ts.createSourceFile(fileName, text, ts.ScriptTarget.ES2022, true, fileName.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
  for (const st of sf.statements) {
    if (!ts.isImportDeclaration(st) || !ts.isStringLiteral(st.moduleSpecifier) || !SPEC_RE.test(st.moduleSpecifier.text)) continue;
    const nb = st.importClause?.namedBindings;
    if (!nb || !ts.isNamedImports(nb) || st.importClause?.isTypeOnly) continue;
    const els = nb.elements;
    const i = els.findIndex((e) => (e.propertyName ?? e.name).text === "hole" && !e.isTypeOnly);
    if (i < 0) continue;
    const local = els[i].name.text;
    let used = false;
    const visit = (n: ts.Node) => {
      if (used || n === st) return;
      if (ts.isIdentifier(n) && n.text === local) used = true;
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

type Narrow = Map<string, { variant?: string; some?: boolean }>;

function pathText(e: ts.Expression): string | null {
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  if (ts.isIdentifier(e)) return e.text;
  if (ts.isPropertyAccessExpression(e) && !e.questionDotToken) {
    const b = pathText(e.expression);
    return b ? `${b}.${e.name.text}` : null;
  }
  return null;
}

const isNullLit = (e: ts.Expression) => e.kind === ts.SyntaxKind.NullKeyword || (ts.isIdentifier(e) && e.text === "undefined");

function terminates(stmts: readonly ts.Statement[]): boolean {
  const last = stmts[stmts.length - 1];
  if (!last) return false;
  if (ts.isReturnStatement(last) || ts.isThrowStatement(last)) return true;
  if (ts.isBlock(last)) return terminates(last.statements);
  if (ts.isIfStatement(last)) return !!last.elseStatement && terminates(blockOf(last.thenStatement)) && terminates(blockOf(last.elseStatement));
  return false;
}
const blockOf = (s: ts.Statement): readonly ts.Statement[] => (ts.isBlock(s) ? s.statements : [s]);

function holeScope(hole: ts.CallExpression, fn: ts.FunctionDeclaration, prog: Program, params: Map<string, VType>): Atom[] {
  const reg = prog.reg;
  const fieldsOf = (t: VType, variant?: string): Field[] => {
    if (t.k === "rec") return reg.rec(t);
    if (t.k === "union") {
      const u = reg.union(t);
      if (variant) return u.variants.find((v) => v.lit === variant)?.fields ?? [];
      return sharedFields(u.variants);
    }
    return [];
  };
  // the (un-narrowed) type of a path p or p.f or p.f.g
  const typeOfPath = (p: string): VType | null => {
    const [head, ...rest] = p.split(".");
    let t = params.get(head) ?? null;
    for (const f of rest) {
      if (!t) return null;
      t = fieldsOf(t).find((x) => x.name === f)?.type ?? null;
    }
    return t;
  };
  // narrowing established by condition `c` evaluating to `pos` (as the translator's `branch` does)
  const cond = (c: ts.Expression, pos: boolean): Narrow => {
    const out: Narrow = new Map();
    while (ts.isParenthesizedExpression(c)) c = c.expression;
    if (ts.isPrefixUnaryExpression(c) && c.operator === ts.SyntaxKind.ExclamationToken) return cond(c.operand, !pos);
    if (ts.isBinaryExpression(c)) {
      const k = c.operatorToken.kind;
      const K = ts.SyntaxKind;
      if ((k === K.AmpersandAmpersandToken && pos) || (k === K.BarBarToken && !pos)) {
        for (const [p, v] of [...cond(c.left, pos), ...cond(c.right, pos)]) if (!out.has(p)) out.set(p, v);
        return out;
      }
      const eq = k === K.EqualsEqualsEqualsToken || k === K.EqualsEqualsToken;
      const neq = k === K.ExclamationEqualsEqualsToken || k === K.ExclamationEqualsToken;
      if (!eq && !neq) return out;
      if (isNullLit(c.left) || isNullLit(c.right)) {
        const p = pathText(isNullLit(c.right) ? c.left : c.right);
        // the value is non-null when the test "is null" is false
        if (p && (pos ? neq : eq)) out.set(p, { some: true });
        return out;
      }
      const tag = (acc: ts.Expression, lit: ts.Expression) => {
        if (!ts.isPropertyAccessExpression(acc) || !ts.isStringLiteralLike(lit)) return;
        const p = pathText(acc.expression);
        const t = p ? typeOfPath(p) : null;
        // only the matching branch is narrowed (the translator does not narrow the complement)
        if (p && t?.k === "union" && reg.union(t).tag === acc.name.text && (pos ? eq : neq)) out.set(p, { variant: lit.text });
      };
      tag(c.left, c.right);
      tag(c.right, c.left);
      return out;
    }
    // truthiness of an optional object/array
    const p = pathText(c);
    const t = p ? typeOfPath(p) : null;
    if (p && pos && t?.k === "opt" && ["rec", "arr", "union", "tuple"].includes(t.elem.k)) out.set(p, { some: true });
    return out;
  };
  const narrowed: Narrow = new Map();
  const add = (m: Narrow) => {
    for (const [p, v] of m) if (!narrowed.has(p)) narrowed.set(p, v);
  };
  let n: ts.Node = hole;
  while (n.parent && n !== fn) {
    const parent = n.parent;
    if (ts.isCaseClause(parent) && parent.statements.includes(n as ts.Statement) && ts.isSwitchStatement(parent.parent.parent)) {
      const sw = parent.parent.parent;
      const clauses = parent.parent.clauses;
      const i = clauses.indexOf(parent);
      const fallsInto = i > 0 && clauses[i - 1].statements.length === 0; // `case "a": case "b": …` — not narrowed
      const p = ts.isPropertyAccessExpression(sw.expression) ? pathText(sw.expression.expression) : null;
      const t = p ? typeOfPath(p) : null;
      if (p && !fallsInto && t?.k === "union" && reg.union(t).tag === (sw.expression as ts.PropertyAccessExpression).name.text && ts.isStringLiteralLike(parent.expression)) {
        add(new Map([[p, { variant: parent.expression.text }]]));
      }
    }
    if (ts.isIfStatement(parent)) {
      if (parent.thenStatement === n) add(cond(parent.expression, true));
      else if (parent.elseStatement === n) add(cond(parent.expression, false));
    }
    if (ts.isConditionalExpression(parent)) {
      if (parent.whenTrue === n) add(cond(parent.condition, true));
      else if (parent.whenFalse === n) add(cond(parent.condition, false));
    }
    // early exits before the hole's statement: `if (c) return …;` narrows by !c
    if ((ts.isBlock(parent) || ts.isCaseClause(parent) || ts.isDefaultClause(parent)) && parent.statements.includes(n as ts.Statement)) {
      const stmts = parent.statements;
      for (let j = stmts.indexOf(n as ts.Statement) - 1; j >= 0; j--) {
        const st = stmts[j];
        if (!ts.isIfStatement(st)) continue;
        const thenExits = terminates(blockOf(st.thenStatement));
        const elseExits = !!st.elseStatement && terminates(blockOf(st.elseStatement));
        if (thenExits && !elseExits) add(cond(st.expression, false));
        else if (elseExits && !thenExits) add(cond(st.expression, true));
      }
    }
    n = parent;
  }
  const scope: Atom[] = [];
  const narrowT = (p: string, t: VType) => (narrowed.get(p)?.some && t.k === "opt" ? t.elem : t);
  for (const [name, t0] of params) {
    const t = narrowT(name, t0);
    scope.push({ code: name, type: t, size: 1 });
    // one level of field access (two for records of records / narrowed variants)
    for (const f of fieldsOf(t, narrowed.get(name)?.variant)) {
      const p = `${name}.${f.name}`;
      const ft = narrowT(p, f.type);
      scope.push({ code: p, type: ft, size: 1 });
      if (ft.k === "rec" || (ft.k === "union" && narrowed.get(p)?.variant)) {
        for (const g of fieldsOf(ft, narrowed.get(p)?.variant)) scope.push({ code: `${p}.${g.name}`, type: narrowT(`${p}.${g.name}`, g.type), size: 2 });
      }
    }
  }
  return scope;
}

/* ───────────────────────── enumeration ───────────────────────── */

export interface Helper {
  name: string;
  params: VType[];
  ret: VType;
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
          for (const pt of [T.int, T.str]) {
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
        if (E.k === "rec" && this.lambdaDepth === 0) {
          const fields = reg.rec(E);
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
          // xs.map((x) => (x.k === v ? { ...x, f: e } : x))
          for (const [i, j, l] of splits(size - 3, 3)) {
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

const BASE_INTS = [-1, 0, 0, 1, 1, 2, 3, 4, 5, 7, 10];
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

function gen(t: VType, prog: Program, pools: Pools, depth = 0): unknown {
  const reg = prog.reg;
  switch (t.k) {
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
      if (Math.random() >= 0.3) return gen(t.elem, prog, pools, depth);
      const a = (t as OptT).absent ?? "null";
      return a === "undefined" || (a === "both" && Math.random() < 0.5) ? undefined : null;
    }
    case "tuple":
      return t.elems.map((e) => gen(e, prog, pools, depth));
    case "rec": {
      const o: Record<string, unknown> = {};
      for (const f of reg.rec(t)) o[f.name] = gen(f.type, prog, pools, depth + 1);
      return o;
    }
    case "union": {
      const u = reg.union(t);
      const v = u.variants[rnd(u.variants.length)];
      const o: Record<string, unknown> = { [u.tag]: v.lit };
      for (const f of v.fields) o[f.name] = gen(f.type, prog, pools, depth + 1);
      return o;
    }
    case "arr": {
      const n = depth > 2 ? 0 : rnd(4);
      const xs = Array.from({ length: n }, () => gen(t.elem, prog, pools, depth + 1));
      // favour distinct ids (common invariant)
      if (t.elem.k === "rec" && xs.length) {
        const ids = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6].sort(() => Math.random() - 0.5);
        xs.forEach((x, i) => {
          if (x && typeof x === "object" && "id" in (x as object) && Math.random() < 0.9) (x as Record<string, unknown>).id = ids[i];
        });
      }
      return xs;
    }
    default:
      return undefined;
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

function makeRunner(sb: Sandbox, target: string, fname: string, paramTypes: VType[], prog: Program, pools: Pools, textFor: (cand: string) => string): Runner {
  // fixed sample set (re-used across candidates; counterexamples are moved to the front)
  const samples: unknown[][] = Array.from({ length: 400 }, () => paramTypes.map((t) => gen(t, prog, pools)));
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
        valid++;
        for (const p of own) {
          let okp = false;
          try {
            okp = !!p(r);
          } catch {
            okp = false;
          }
          if (!okp) {
            samples.unshift(samples.splice(i, 1)[0]); // counterexample first next time
            return { ok: false, valid, why: `postcondition fails on ${JSON.stringify(args)} ↦ ${JSON.stringify(r)}`, cat: "postcondition fails" };
          }
        }
      }
      if (valid > 0) return { ok: true, valid };
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

/* ───────────────────────── command ───────────────────────── */

export { Enumerator };

export interface SynthResult {
  fn: string;
  hole: string;
  solution: string | null;
  tested: number;
  proved: boolean;
  /** proved | not-proved | skipped */
  status: string;
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
  const bom = raw.startsWith("\uFEFF") ? "\uFEFF" : "";
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
        const lk = runLake(cfg.outDir);
        c = { tr, v: judge(tr.obligations, lk.messages, findMarkers(cfg.outDir), cfg.outDir), diag: "" };
      }
      checks.set(text, c);
    }
    return c;
  };

  // ---- the program must translate before synthesis (holes are fine: they become sorry) ----
  const baseTr = translate({ ...cfg, overrides: new Map([[target, base]]) } as Config);
  if (!baseTr.ok) {
    console.log("synth needs a project that translates (holes may stay); fix these first:");
    for (const d of [...baseTr.tsDiagnostics, ...baseTr.errors.map(fmtErr)]) console.log("  " + d);
    process.exitCode = 1;
    return results;
  }

  // ---- program, holes, tasks ----
  const options: ts.CompilerOptions = { strict: true, jsx: ts.JsxEmit.ReactJSX, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, skipLibCheck: true, noEmit: true, allowImportingTsExtensions: true };
  const program = ts.createProgram(cfg.files, options, overrideHost(options, new Map([[target, base]])));
  const checker = program.getTypeChecker();
  const prog = new Program(checker, root, (sf) => "VTS." + path.relative(cfg.srcDir, sf.fileName).replace(/\.(tsx?)$/, "").split(path.sep).join("."));
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

  // functions referenced (transitively) by a declaration, any file of the program
  const refsCache = new Map<ts.Node, Set<ts.FunctionDeclaration>>();
  const refsOf = (d: ts.FunctionDeclaration): Set<ts.FunctionDeclaration> => {
    const done = refsCache.get(d);
    if (done) return done;
    const out = new Set<ts.FunctionDeclaration>();
    refsCache.set(d, out);
    const visit = (n: ts.Node) => {
      if (ts.isIdentifier(n)) {
        let s = checker.getSymbolAtLocation(n);
        if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
        const dd = s?.declarations?.[0];
        if (dd && dd !== d && ts.isFunctionDeclaration(dd) && ts.isSourceFile(dd.parent) && !out.has(dd)) {
          out.add(dd);
          for (const x of refsOf(dd)) out.add(x);
        }
      }
      ts.forEachChild(n, visit);
    };
    if (d.body) visit(d.body);
    return out;
  };
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
      const pending = [...refsOf(t.fn)].filter((d) => holesIn(d).some((h) => ![...fills.keys()].some((x) => x.node === h))).map((d) => d.name?.text ?? "?");
      return { status: "pending", why: pending.length ? `its proof depends on unfinished code (hole) in ${pending.join(", ")}` : `its proof depends on a sorry (a hole or an unfinished proof it relies on)` };
    }
    const relative = [...new Set(names.flatMap((q) => v.axioms.get(q)!))].filter((a) => !STD_AXIOMS.has(a));
    return { status: "proved", relative };
  };

  for (const task of ordered) {
    const fd = task.fn;
    const holesLabel = task.holes.length > 1 ? `${task.holes.length} holes in ${task.name}` : `hole in ${task.name}`;
    const record = (h: Hole, solution: string | null, tested: number, status: string, note?: string) => {
      results.push({ fn: task.name, hole: showType(h.type), solution, tested, proved: status === "proved", status, note });
    };
    if (isTrusted(fd)) {
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", "@trusted");
      console.log(`  ✗ ${task.name} is /** @trusted */: Lean checks nothing in its body, so a fill could not be proved. Remove @trusted to synthesize it.`);
      continue;
    }
    if (isComponent(fd)) {
      console.log(`${holesLabel}`);
      for (const h of task.holes) record(h, null, 0, "skipped", "component");
      console.log(`  ✗ ${task.name} looks like a component: synth fills holes in model functions; move the expression into one`);
      continue;
    }
    // types, scope, helpers
    let params: Map<string, VType>;
    const helpers: Helper[] = [];
    try {
      params = paramTypes(fd);
      for (const h of task.holes) h.scope = holeScope(h.node, fd, prog, params);
      for (const st of sf.statements) {
        if (!ts.isFunctionDeclaration(st) || !st.name || st === fd || !st.type) continue;
        if (/^[A-Z]/.test(st.name.text)) continue;
        const hasPre = st.body?.statements.some((x) => ts.isExpressionStatement(x) && ts.isCallExpression(x.expression) && specFn(env, x.expression.expression) === "requires");
        // (a function whose holes were filled above is a helper like any other)
        if (hasPre || st.parameters.some((p) => !p.type) || holesIn(st).some((x) => ![...accepted.keys()].some((a) => a.node === x))) continue;
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
    for (const st of fd.body?.statements ?? []) {
      if (!ts.isExpressionStatement(st) || !ts.isCallExpression(st.expression)) break;
      const callee = st.expression.expression;
      const k = specFn(env, callee);
      if (k === "ensures") {
        ownContract.push({ at: [callee.getStart(sf), callee.getEnd()], text: OWN_ENSURES });
        task.ensures++;
      } else if (k === "requires") ownContract.push({ at: [callee.getStart(sf), callee.getEnd()], text: OWN_REQUIRES });
      else if (k !== "decreases") break;
    }
    const pools = harvest(fd);
    const t0All = Date.now();
    const deadline = t0All + TIME_LIMIT_MS * (task.holes.length + 1);
    let blocked: string | null = null;
    const notes = new Map<Hole, { tested: number; last?: string; cand?: string }>();

    // search hole i of the task with the earlier holes tentatively filled
    const solve = async (i: number, tentative: Map<Hole, string>): Promise<Map<Hole, string> | null> => {
      const h = task.holes[i];
      const last = i === task.holes.length - 1;
      const ctx = [...tentative].map(([x, c]) => `hole ${task.holes.indexOf(x) + 1} = ${c}`).join(", ");
      const label = task.holes.length > 1 ? `hole ${i + 1}/${task.holes.length} in ${task.name}${ctx ? ` (with ${ctx})` : ""}` : `hole in ${task.name}`;
      console.log(`${label}: ${showType(h.type)}   scope: ${h.scope.map((a) => a.code).join(", ")}`);
      const en = new Enumerator(prog, h.scope, h.type, maxSize);
      for (const hp of helpers) {
        en.helpers.push(hp);
        hp.params.forEach((t) => en.register(t));
      }
      const fills = (cand: string) => new Map([...accepted, ...tentative, [h, fillText(h, cand)]]);
      const runner = makeRunner(sb!, target, task.name, pTypes as VType[], prog, pools, (cand) => applyEdits(base, [...editsOf(fills(cand)), ...ownContract]));
      // ---- enumerate & test ----
      let tested = 0;
      let passed = 0;
      let sizeReached = 0;
      let stop = "";
      let untestable: string | null = null;
      let untested = 0;
      let searchMs = 0;
      const fails = new Map<string, { n: number; example: string }>();
      const leanRejected: string[] = [];
      let leanChecks = 0;
      let examined = 0;
      const limitFor = Math.min(TIME_LIMIT_MS, Math.max(5000, deadline - Date.now()));
      // with several holes, a rejection may be the fault of an earlier fill: backtrack sooner
      const leanCap = task.holes.length > 1 ? MAX_LEAN_CHECKS_JOINT : MAX_LEAN_CHECKS;
      const survivors = function* (): Generator<{ code: string; valid: number; untested?: boolean }> {
        // search time excludes the Lean checks done while the generator is suspended
        let resume = Date.now();
        const pause = () => {
          searchMs += Date.now() - resume;
          resume = -1;
        };
        try {
          for (let size = 1; size <= maxSize; size++) {
            sizeReached = size;
            const terms = en.build(h.type, size);
            for (const c of terms) {
              if (searchMs + (Date.now() - resume) > limitFor) {
                stop = `the ${(limitFor / 1000).toFixed(0)}s time limit was reached at size ${size}`;
                return;
              }
              if (tested >= MAX_CANDIDATES) {
                stop = `the cap of ${MAX_CANDIDATES} candidates was reached at size ${size}`;
                return;
              }
              if (untestable) {
                // the inputs cannot exercise this hole: the smallest candidates go to Lean untested
                if (untested++ >= MAX_UNTESTED) {
                  stop = `${MAX_UNTESTED} untested candidates were tried`;
                  return;
                }
                pause();
                yield { code: c.code, valid: 0, untested: true };
                resume = Date.now();
                continue;
              }
              tested++;
              const r = runner.run(c.code);
              if (process.env.VREACT_SYNTH_DEBUG && tested <= 12) console.log(`    [${r.ok ? "pass" : "fail"}] ${c.code}  ${r.why ?? ""}`);
              if (r.untestable) {
                untestable = r.untestable;
                console.log(`  ${r.untestable}: the smallest candidates are checked by Lean only`);
                untested++;
                pause();
                yield { code: c.code, valid: 0, untested: true };
                resume = Date.now();
                continue;
              }
              if (!r.ok) {
                const cat = r.cat ?? "fails";
                const e = fails.get(cat) ?? { n: 0, example: `${c.code}: ${r.why}` };
                e.n++;
                fails.set(cat, e);
                continue;
              }
              passed++;
              pause();
              yield { code: c.code, valid: r.valid };
              resume = Date.now();
            }
          }
          stop = `all candidates up to size ${maxSize} were tried` + (en.capped ? ` (sub-expression lists were capped at ${MAX_TERMS} per type and size, so some larger candidates were never built)` : "");
        } finally {
          if (resume >= 0) pause();
        }
      };
      let solved: Map<Hole, string> | null = null;
      for (const s of survivors()) {
        if (blocked) break;
        examined++;
        const ins = fillText(h, s.code);
        notes.set(h, { tested, cand: ins });
        const after = `(${tested} candidate(s) tested in ${(searchMs / 1000).toFixed(1)}s)`;
        if (!s.untested) console.log(`  candidate passes ${s.valid} random tests: ${ins}   ${after}`);
        else console.log(`  untested candidate: ${ins}`);
        if (!last) {
          console.log(`  … proof pending the other hole(s) of ${task.name}: searching hole ${i + 2} with this fill`);
          solved = await solve(i + 1, new Map([...tentative, [h, ins]]));
          if (solved || blocked) break;
          if (examined >= MAX_TENTATIVE) {
            stop = `${MAX_TENTATIVE} fills of this hole were tried with the next one`;
            break;
          }
          continue;
        }
        const all = fills(s.code);
        const text = leanText(all);
        const st = statusOf(check(text), text, task, all);
        if (st.status === "untranslatable") {
          console.log(`  ✗ ${ins}: does not translate: ${st.why}`);
          leanRejected.push(ins);
        } else {
          leanChecks++;
          if (st.status === "proved") {
            const rel2 = st.relative.length ? ` (relative to: ${st.relative.join(", ")})` : "";
            console.log(task.holes.length > 1 ? `  ✔ proved by Lean: ${task.name} with ${[...tentative.values(), ins].join(" / ")}${rel2}` : `  ✔ proved by Lean: ${ins}${rel2}`);
            solved = all;
            break;
          }
          if (st.status === "rejected") {
            console.log(`  ✗ Lean rejects ${ins}: ${st.why}`);
            leanRejected.push(ins);
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
      notes.set(h, { ...notes.get(h), tested, last: stop });
      if (!solved && !blocked) {
        const top = [...fails.entries()].sort((a, b) => b[1].n - a[1].n)[0];
        const what = untestable ?? (passed ? `${passed} candidate(s) passed the tests, none was proved` : "no candidate passed the tests");
        console.log(`  ${tested} candidates tested in ${(searchMs / 1000).toFixed(1)}s, up to size ${sizeReached}; stopped: ${stop || "search exhausted"}`);
        console.log(`  no verified solution for ${label}: ${what}`);
        if (top && !passed) console.log(`  most common failure (${top[1].n}×): ${top[1].example}`);
        if (last || !passed)
          console.log(
            leanRejected.length
              ? "  the random tests accept candidates that Lean rejects: write this one by hand"
              : "  write this one by hand (synth builds straight-line expressions; guarded updates need an `if`), or check that the spec is satisfiable",
          );
      }
      return solved;
    };

    const solution = await solve(0, new Map());
    if (solution) {
      for (const h of task.holes) {
        accepted.set(h, solution.get(h)!);
        record(h, solution.get(h)!, notes.get(h)?.tested ?? 0, "proved");
      }
      acceptedTasks.push(task);
    } else {
      for (const h of task.holes) {
        const n = notes.get(h);
        record(h, null, n?.tested ?? 0, "not-proved", blocked ? `${n?.cand ? `${n.cand} passes the tests, but ` : ""}${blocked}` : n?.last);
      }
      if (task.holes.length > 1) console.log(`  (no hole of ${task.name} is filled: its holes are only proved together)`);
    }
  }

  // ---- result: the written text is exactly the one Lean checked ----
  if (accepted.size) {
    const final = leanText(accepted);
    // the last check of each accepted function may predate later fills: re-check the final text once
    const c = check(final);
    const bad = acceptedTasks.map((t) => [t, statusOf(c, final, t, accepted)] as const).filter(([, s]) => s.status !== "proved");
    if (bad.length) {
      for (const [t, s] of bad) console.log(`✗ ${t.name} is no longer proved in the final program (${s.status}: ${"why" in s ? s.why : ""}): nothing written`);
      for (const r of results) if (bad.some(([t]) => t.name === r.fn)) Object.assign(r, { proved: false, status: "not-proved" });
    } else if (opts.write) {
      if (fs.readFileSync(target, "utf8") !== raw) console.log(`✗ ${rel} changed while synth was running: not written`);
      else {
        fs.writeFileSync(target, bom + final);
        console.log(`wrote ${rel}`);
      }
    } else console.log(`(${rel} not modified: rerun with --write to keep the proved fill(s))`);
  }
  if (opts.json) console.log(JSON.stringify(results, null, 2));
  return results;
}
