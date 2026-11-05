/**
 * vreact synth — fill `hole<T>()` placeholders against the function's contract.
 *
 *   1. Scope: parameters of the enclosing function, refined by the narrowing in
 *      effect at the hole (switch/if on a discriminant, null tests).
 *   2. Enumerate well-typed VTS expressions of type T, smallest first, from a
 *      grammar of idiomatic immutable updates: field updates `{ ...s, f: e }`,
 *      append `[...xs, e]`, remove-by-key `xs.filter(x => x.k !== v)`,
 *      update-by-key `xs.map(x => x.k === v ? { ...x, f: e } : x)`, record and
 *      variant literals, ±1 arithmetic, comparisons.
 *   3. Test each candidate by *running the real transpiled JavaScript* on random
 *      inputs: `requires` filters inputs, `ensures` must hold on the result
 *      (counterexample-driven pruning).
 *   4. Prove the surviving candidates with Lean (`vreact verify`), in order; the
 *      first one whose obligations all hold is the answer.
 */
import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { loadConfig } from "./cli.ts";
import { translate } from "./module.ts";
import { runLake, findMarkers, judge } from "./lean.ts";
import { Program, ModCtx } from "./ctx.ts";
import { type VType, type Field, T, typeOfNode, showType, sharedFields } from "./types.ts";
import { specFn } from "./translate.ts";
import { baseEnv } from "./component.ts";

interface Atom {
  code: string;
  type: VType;
  size: number;
}

interface Hole {
  node: ts.CallExpression;
  type: VType;
  fn: ts.FunctionDeclaration;
  scope: Atom[];
}

const key = (t: VType) => JSON.stringify(t);
const MAX_TERMS = 3000;
const MAX_CANDIDATES = 30000;
const TIME_LIMIT_MS = 60000;

/* ───────────────────────── scope at the hole ───────────────────────── */

function holeScope(hole: ts.CallExpression, fn: ts.FunctionDeclaration, prog: Program): Atom[] {
  const reg = prog.reg;
  const scope: Atom[] = [];
  const params = new Map<string, VType>();
  for (const p of fn.parameters) {
    if (!ts.isIdentifier(p.name) || !p.type) continue;
    const t = typeOfNode(p.type, prog.typeEnv, "P");
    params.set(p.name.text, t);
  }
  // narrowing in effect at the hole
  const narrowed = new Map<string, { variant?: string; some?: boolean }>();
  let n: ts.Node = hole;
  while (n.parent && n !== fn) {
    const parent = n.parent;
    if (ts.isCaseClause(parent) && ts.isCaseBlock(parent.parent) && ts.isSwitchStatement(parent.parent.parent)) {
      const sw = parent.parent.parent;
      const e = sw.expression;
      if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression) && ts.isStringLiteralLike(parent.expression)) {
        narrowed.set(e.expression.text, { variant: parent.expression.text });
      }
    }
    if (ts.isIfStatement(parent) && parent.thenStatement === n) {
      const c = parent.expression;
      if (ts.isBinaryExpression(c) && c.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken) {
        if (ts.isPropertyAccessExpression(c.left) && ts.isIdentifier(c.left.expression) && ts.isStringLiteralLike(c.right)) {
          narrowed.set(c.left.expression.text, { variant: c.right.text });
        }
      }
      if (ts.isBinaryExpression(c) && c.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsEqualsToken && c.right.kind === ts.SyntaxKind.NullKeyword && ts.isIdentifier(c.left)) {
        narrowed.set(c.left.text, { some: true });
      }
    }
    n = parent;
  }
  for (const [name, t0] of params) {
    let t = t0;
    const nr = narrowed.get(name);
    if (nr?.some && t.k === "opt") t = t.elem;
    scope.push({ code: name, type: t, size: 1 });
    // one level of field access (two for records of records)
    const fieldsOf = (t: VType): Field[] => {
      if (t.k === "rec") return reg.rec(t);
      if (t.k === "union") {
        const u = reg.union(t);
        if (nr?.variant) return u.variants.find((v) => v.lit === nr.variant)?.fields ?? [];
        return sharedFields(u.variants);
      }
      return [];
    };
    for (const f of fieldsOf(t)) {
      scope.push({ code: `${name}.${f.name}`, type: f.type, size: 1 });
      if (f.type.k === "rec") for (const g of reg.rec(f.type)) scope.push({ code: `${name}.${f.name}.${g.name}`, type: g.type, size: 2 });
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
      case "opt":
        return ["null"];
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
    return sub.terms(ft, size).map((a) => a.code).filter((c) => /\bx\b/.test(c) || size === 1);
  }
}

function wrap(code: string): string {
  return /^[\w.$]+$/.test(code) ? code : `(${code})`;
}

/* ───────────────────────── random inputs ───────────────────────── */

function rnd(n: number) {
  return Math.floor(Math.random() * n);
}

function gen(t: VType, prog: Program, depth = 0): unknown {
  const reg = prog.reg;
  switch (t.k) {
    case "int":
      return [-1, 0, 0, 1, 1, 2, 3, 4, 5, 7, 10][rnd(11)];
    case "num":
      return Math.random() * 10 - 2;
    case "bool":
      return Math.random() < 0.5;
    case "str":
      return ["", "a", "b", "ab", " a ", "hello", "x y"][rnd(7)];
    case "enum": {
      const lits = reg.enumLits(t);
      return lits[rnd(lits.length)];
    }
    case "opt":
      return Math.random() < 0.3 ? null : gen(t.elem, prog, depth);
    case "tuple":
      return t.elems.map((e) => gen(e, prog, depth));
    case "rec": {
      const o: Record<string, unknown> = {};
      for (const f of reg.rec(t)) o[f.name] = gen(f.type, prog, depth + 1);
      return o;
    }
    case "union": {
      const u = reg.union(t);
      const v = u.variants[rnd(u.variants.length)];
      const o: Record<string, unknown> = { [u.tag]: v.lit };
      for (const f of v.fields) o[f.name] = gen(f.type, prog, depth + 1);
      return o;
    }
    case "arr": {
      const n = depth > 2 ? 0 : rnd(4);
      const xs = Array.from({ length: n }, () => gen(t.elem, prog, depth + 1));
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

interface Runner {
  run(candidate: string): Promise<{ ok: boolean; valid: number; why?: string }>;
}

function transpileProject(cfg: ReturnType<typeof loadConfig>, outDir: string, skip: string) {
  fs.mkdirSync(outDir, { recursive: true });
  for (const f of cfg.files) {
    if (f === skip) continue;
    const src = fs.readFileSync(f, "utf8");
    writeJs(src, f, cfg.srcDir, outDir);
  }
}

function writeJs(src: string, file: string, srcDir: string, outDir: string, suffix = ""): string {
  const js = ts.transpileModule(src, {
    compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022, jsx: ts.JsxEmit.ReactJSX, verbatimModuleSyntax: false },
    fileName: file,
  }).outputText.replace(/from\s+["'](\.{1,2}\/[^"']+)["']/g, (_m, p) => `from "${p.replace(/\.(tsx?|jsx?)$/, "")}.js"`);
  const rel = path.relative(srcDir, file).replace(/\.(tsx?)$/, suffix + ".js");
  const out = path.join(outDir, rel);
  fs.mkdirSync(path.dirname(out), { recursive: true });
  fs.writeFileSync(out, js);
  return out;
}

let candidateCounter = 0;

function makeRunner(cfg: ReturnType<typeof loadConfig>, file: string, hole: Hole, prog: Program, at: [number, number], src: string): Runner {
  const outDir = path.join(cfg.outDir, "synth-js");
  transpileProject(cfg, outDir, file);
  const fname = hole.fn.name!.text;
  const paramTypes = hole.fn.parameters.map((p) => typeOfNode(p.type!, prog.typeEnv, "P"));
  // fixed sample set (re-used across candidates; counterexamples are moved to the front)
  const samples: unknown[][] = Array.from({ length: 400 }, () => paramTypes.map((t) => gen(t, prog)));
  return {
    async run(candidate) {
      const code = src.slice(0, at[0]) + `(${candidate})` + src.slice(at[1]);
      const out = writeJs(code, file, cfg.srcDir, outDir, `.c${++candidateCounter}`);
      let mod: Record<string, unknown>;
      try {
        mod = await import(pathToFileURL(out).href);
      } catch (e) {
        return { ok: false, valid: 0, why: "does not load: " + (e as Error).message };
      } finally {
        fs.rmSync(out, { force: true });
      }
      const f = mod[fname] as ((...a: unknown[]) => unknown) | undefined;
      if (typeof f !== "function") return { ok: false, valid: 0, why: `${fname} must be exported` };
      let valid = 0;
      for (let i = 0; i < samples.length; i++) {
        const args = structuredClone(samples[i]);
        const t: { posts: ((r: unknown) => boolean)[] } = { posts: [] };
        (globalThis as Record<string, unknown>).__VREACT_TEST__ = t;
        let r: unknown;
        try {
          r = f(...args);
        } catch (e) {
          if ((e as Error)?.constructor?.name === "PreconditionFailed") continue;
          samples.unshift(samples.splice(i, 1)[0]);
          return { ok: false, valid, why: "throws: " + (e as Error).message };
        } finally {
          (globalThis as Record<string, unknown>).__VREACT_TEST__ = undefined;
        }
        valid++;
        for (const p of t.posts) {
          let okp = false;
          try {
            okp = !!p(r);
          } catch {
            okp = false;
          }
          if (!okp) {
            samples.unshift(samples.splice(i, 1)[0]); // counterexample first next time
            return { ok: false, valid, why: `postcondition fails on ${JSON.stringify(args)} ↦ ${JSON.stringify(r)}` };
          }
        }
      }
      return { ok: valid > 0, valid, why: valid ? undefined : "no input satisfies the precondition" };
    },
  };
}

/* ───────────────────────── command ───────────────────────── */

export { Enumerator };
export async function synthCommand(root: string, files: string[], opts: { write?: boolean; json?: boolean; maxSize?: number }) {
  if (!files.length) throw new Error("usage: vreact synth <file.tsx> [--write]");
  const cfg = loadConfig(root);
  const file = path.resolve(root, files[0]);
  const original = fs.readFileSync(file, "utf8");
  const results: { fn: string; hole: string; solution: string | null; tested: number; proved: boolean }[] = [];
  let src = original;
  let skip = 0; // holes (in source order) left unsolved
  for (;;) {
    // (re)load the program for the current source
    const program = ts.createProgram(cfg.files, { strict: true, jsx: ts.JsxEmit.ReactJSX, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, skipLibCheck: true, noEmit: true });
    const checker = program.getTypeChecker();
    const prog = new Program(checker, root, (sf) => "VTS." + path.relative(cfg.srcDir, sf.fileName).replace(/\.(tsx?)$/, "").split(path.sep).join("."));
    const sf = program.getSourceFile(file)!;
    const m = new ModCtx(prog, "VTS.Synth", sf, [], { n: 0 });
    const env = baseEnv(m);
    let found: ts.CallExpression | null = null;
    let seen = 0;
    const visit = (n: ts.Node) => {
      if (!found && ts.isCallExpression(n) && specFn(env, n.expression) === "hole") {
        if (seen++ === skip) found = n;
      }
      if (!found) ts.forEachChild(n, visit);
    };
    visit(sf);
    if (!found) break;
    const holeNode = found as ts.CallExpression;
    let fn: ts.Node = holeNode;
    while (fn && !ts.isFunctionDeclaration(fn)) fn = fn.parent;
    if (!fn) throw new Error("hole() must be inside a top-level function");
    const fd = fn as ts.FunctionDeclaration;
    if (!holeNode.typeArguments?.[0]) throw new Error(`${fd.name?.text}: write hole<T>() with an explicit type`);
    // register all types of the module
    for (const st of sf.statements) if (ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) typeOfNode(ts.factory.createTypeReferenceNode(st.name), prog.typeEnv, st.name.text);
    const holeT = typeOfNode(holeNode.typeArguments[0], prog.typeEnv, "Hole");
    const scope = holeScope(holeNode, fd, prog);
    const hole: Hole = { node: holeNode, type: holeT, fn: fd, scope };
    const at: [number, number] = [holeNode.getStart(sf), holeNode.getEnd()];
    console.log(`hole in ${fd.name!.text}: ${showType(holeT)}   scope: ${scope.map((a) => a.code).join(", ")}`);
    const runner = makeRunner(cfg, file, hole, prog, at, src);
    const en = new Enumerator(prog, scope, holeT, opts.maxSize ?? 9);
    // helper functions of the module (total ones, not the function being synthesized)
    for (const st of sf.statements) {
      if (!ts.isFunctionDeclaration(st) || !st.name || st === fd || !st.type) continue;
      if (/^[A-Z]/.test(st.name.text)) continue;
      const hasPre = st.body?.statements.some((x) => ts.isExpressionStatement(x) && ts.isCallExpression(x.expression) && specFn(env, x.expression.expression) === "requires");
      if (hasPre || st.parameters.some((p) => !p.type)) continue;
      try {
        const h = { name: st.name.text, params: st.parameters.map((p) => typeOfNode(p.type!, prog.typeEnv, "P")), ret: typeOfNode(st.type, prog.typeEnv, "R") };
        en.helpers.push(h);
        h.params.forEach((t) => en.register(t));
      } catch {
        /* unsupported signature: skip */
      }
    }
    const survivors: string[] = [];
    let tested = 0;
    const t0 = Date.now();
    outer: for (let size = 1; size <= (opts.maxSize ?? 9); size++) {
      if (tested > MAX_CANDIDATES || Date.now() - t0 > TIME_LIMIT_MS) {
        console.log(`  search budget exhausted at size ${size}`);
        break;
      }
      // top level: complete list of this size (subterms are capped, the budget bounds the search)
      const terms = en.build(holeT, size);
      for (const c of terms) {
        if (tested > MAX_CANDIDATES || Date.now() - t0 > TIME_LIMIT_MS) break;
        tested++;
        const r = await runner.run(c.code);
        if (process.env.VREACT_SYNTH_DEBUG && tested <= 12) console.log(`    [${r.ok ? "pass" : "fail"}] ${c.code}  ${r.why ?? ""}`);
        if (r.ok) {
          survivors.push(c.code);
          console.log(`  candidate passes ${r.valid} random tests: ${c.code}`);
          if (survivors.length >= 3) break outer;
        }
      }
      if (survivors.length) break;
    }
    console.log(`  ${tested} candidates tested in ${((Date.now() - t0) / 1000).toFixed(1)}s`);
    let solution: string | null = null;
    for (const cand of survivors) {
      const attempt = src.slice(0, at[0]) + cand + src.slice(at[1]);
      fs.writeFileSync(file, attempt);
      const tr = translate(cfg);
      if (!tr.ok) {
        console.log(`  ✗ ${cand}: does not translate: ${[...tr.tsDiagnostics, ...tr.errors.map((e) => e.message)].join("; ")}`);
        continue;
      }
      const lk = runLake(cfg.outDir);
      const v = judge(tr.obligations, lk.messages, findMarkers(cfg.outDir), cfg.outDir);
      const start = sf.getLineAndCharacterOfPosition(fd.getStart(sf)).line + 1;
      const end = sf.getLineAndCharacterOfPosition(fd.getEnd()).line + 1;
      const rel = path.relative(root, file);
      const mine = v.failed.filter((f) => f.ob.where.startsWith(rel + ":") && f.ob.line >= start && f.ob.line <= end);
      if (mine.length === 0 && v.internal.length === 0) {
        solution = cand;
        console.log(`  ✔ proved by Lean: ${cand}`);
        break;
      }
      console.log(`  ✗ Lean rejects ${cand}: ${mine.map((f) => f.ob.desc).join("; ")}`);
    }
    results.push({ fn: fd.name!.text, hole: showType(holeT), solution, tested, proved: !!solution });
    if (!solution) {
      fs.writeFileSync(file, src);
      console.log(`  no verified solution found up to size ${opts.maxSize ?? 9}: write this one by hand (or strengthen the spec)`);
      skip++;
      continue;
    }
    src = src.slice(0, at[0]) + solution + src.slice(at[1]);
    fs.writeFileSync(file, src);
  }
  if (!opts.write) fs.writeFileSync(file, original);
  else if (src !== original) console.log(`wrote ${path.relative(root, file)}`);
  if (opts.json) console.log(JSON.stringify(results, null, 2));
  return results;
}
