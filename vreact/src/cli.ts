#!/usr/bin/env node
/**
 * vreact — formally verified React (VTS → Lean 4).
 *
 *   vreact verify  [--root DIR] [--json] [--full] [--quiet]   translate, check with Lean, report
 *   vreact translate [--root DIR]                     only generate the Lean project
 *   vreact synth <file.tsx> [--root DIR] [--write]    fill hole() placeholders (see synth.ts)
 *   vreact explain <file.tsx> [--root DIR]            print the generated Lean for a module
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { translate, type Config, type TranslateResult } from "./module.ts";
import { runLake, findMarkers, judge, summarizeLeanError, type Verdict, type ErrorCause, type LeanMessage } from "./lean.ts";
import { VtsError } from "./util.ts";
import { editorProject } from "./ide.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_LIB = path.resolve(here, "..", "lean");

interface ProjectConfig {
  src?: string;
  include?: string[];
  exclude?: string[];
  proofs?: string;
  out?: string;
  /** heartbeat budget (in thousands) of each proof obligation; default 1000000 */
  heartbeats?: number;
}

export function loadConfig(root: string, only?: string[]): Config {
  const cfgFile = path.join(root, "vreact.json");
  let pc: ProjectConfig = {};
  if (fs.existsSync(cfgFile)) {
    try {
      pc = JSON.parse(fs.readFileSync(cfgFile, "utf8"));
    } catch (e) {
      throw new Error(`${cfgFile} is not valid JSON: ${e instanceof Error ? e.message : e}`);
    }
    if (typeof pc !== "object" || pc === null || Array.isArray(pc)) throw new Error(`${cfgFile}: expected an object such as { "src": "src" }`);
  }
  if (pc.heartbeats !== undefined && !(Number.isInteger(pc.heartbeats) && pc.heartbeats >= 0)) throw new Error(`${cfgFile}: "heartbeats" must be a non-negative integer (thousands of heartbeats per obligation)`);
  const srcDir = path.resolve(root, pc.src ?? "src");
  if (!pc.include && !(fs.existsSync(srcDir) && fs.statSync(srcDir).isDirectory()))
    throw new Error(`no source directory ${srcDir}: run vreact in the project directory (or pass --root DIR), or set "src" in vreact.json`);
  const exclude = new Set((pc.exclude ?? ["main.tsx", "main.ts", "vite-env.d.ts"]).map((e) => path.resolve(srcDir, e)));
  const files: string[] = [];
  const walk = (d: string) => {
    for (const f of fs.readdirSync(d).sort()) {
      const p = path.join(d, f);
      if (fs.statSync(p).isDirectory()) {
        if (f !== "node_modules" && !f.startsWith(".")) walk(p);
      } else if (/\.(ts|tsx)$/.test(f) && !/\.d\.ts$|\.test\.|\.spec\./.test(f) && !exclude.has(p)) files.push(p);
    }
  };
  if (pc.include) for (const inc of pc.include) files.push(path.resolve(root, inc));
  else walk(srcDir);
  return {
    root,
    srcDir,
    files: only?.length ? files.filter((f) => only.some((o) => path.resolve(root, o) === f)) : files,
    outDir: path.resolve(root, pc.out ?? ".vreact"),
    proofsDir: path.resolve(root, pc.proofs ?? "proofs"),
    leanLib: LEAN_LIB,
    ...(pc.heartbeats !== undefined ? { heartbeats: pc.heartbeats } : {}),
  };
}

const C = process.stdout.isTTY
  ? { g: (s: string) => `\x1b[32m${s}\x1b[0m`, r: (s: string) => `\x1b[31m${s}\x1b[0m`, y: (s: string) => `\x1b[33m${s}\x1b[0m`, d: (s: string) => `\x1b[2m${s}\x1b[0m`, b: (s: string) => `\x1b[1m${s}\x1b[0m` }
  : { g: (s: string) => s, r: (s: string) => s, y: (s: string) => s, d: (s: string) => s, b: (s: string) => s };

function relp(root: string, f: string) {
  return path.relative(root, f);
}

/**
 * lean-toolchain and lakefile.toml in the app folder for Lean editors (ide.ts), once the
 * generated project is written; a failure is reported, never a reason to stop verifying.
 */
function editorFiles(cfg: Config, print: boolean) {
  try {
    const r = editorProject(cfg.root, cfg.outDir, cfg.proofsDir, cfg.leanLib);
    if (print) for (const n of r.notes) console.log(C.d(n));
  } catch (e) {
    if (print) console.log(C.y(`could not write the Lean editor files (lakefile.toml, lean-toolchain): ${e instanceof Error ? e.message : e}`));
  }
}

function printTranslationErrors(tr: TranslateResult, root: string) {
  for (const d of tr.tsDiagnostics) console.log(C.r("✗ TS  ") + d);
  for (const e of tr.errors) {
    console.log(C.r("✗ VTS ") + `${e.file ? relp(root, e.file) : "?"}:${e.line}:${e.col}: ${e.message}`);
  }
}

const STD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);

export type Status = "verified" | "relative" | "trusted" | "assumes" | "incomplete" | "unchecked";

/** `assume(…)` facts: the axiom `VReact.assumed` (printed `assumed` under `open VReact`). */
const ASSUMED = new Set(["VReact.assumed", "assumed"]);

/**
 * An axiom of native evaluation: Lean admits the result of compiled code as an axiom
 * `<decl>._native.<tactic>.ax_…` (`native_decide`, `decide +native`, `bv_decide`), or through
 * `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler`. Such a proof trusts Lean's
 * compiler (and every `@[implemented_by]`/`@[extern]`) instead of the kernel; user proofs may
 * not use it (`ProofCheck.lean`), and wherever it shows the item is not verified.
 */
export function isNativeAxiom(a: string): boolean {
  const parts = a.split(".");
  return parts.includes("_native") || (["ofReduceBool", "ofReduceNat", "trustCompiler"].includes(parts[parts.length - 1]) && (parts.length === 1 || (parts.length === 2 && parts[0] === "Lean")));
}

/**
 * `trustedAxioms`: the axioms the translator emits for @trusted declarations; any other
 * axiom (outside Lean's standard ones and `VReact.assumed`, e.g. one declared in a user
 * proof, also in a `VTS.` namespace) makes the item TRUSTED, never VERIFIED* — except one of
 * native evaluation, which makes it INCOMPLETE (and the verdict NOT VERIFIED, see `reportFrom`).
 * `VReact.assumed` stands for the program's `assume(…)` facts (ASSUMES) only where
 * `#vreact_assumed` (`outside`) found no declaration outside the generated code that uses it
 * directly: a user proof that does is an axiom of its own (TRUSTED), and without that report
 * the item is not checked.
 */
function classify(axioms: string[] | undefined, own: string, trustedAxioms: Set<string>, outside: string[] | undefined): Status {
  if (!axioms) return "unchecked";
  if (axioms.includes("sorryAx") || axioms.some(isNativeAxiom)) return "incomplete";
  const assumed = axioms.some((a) => ASSUMED.has(a));
  if (assumed && outside === undefined) return "unchecked";
  const vts = axioms.filter((a) => trustedAxioms.has(a));
  if (vts.some((a) => a === own || a.startsWith(own + "."))) return "trusted";
  if (axioms.some((a) => !STD_AXIOMS.has(a) && !ASSUMED.has(a) && !trustedAxioms.has(a))) return "trusted";
  if (assumed && outside!.length) return "trusted";
  if (assumed) return "assumes";
  // only trusted *dependencies* (not the declaration's own namespace): verified relative to them
  if (vts.length) return "relative";
  return "verified";
}

const ORDER: Status[] = ["unchecked", "incomplete", "trusted", "assumes", "relative", "verified"];
const worst = (sts: Status[]) => sts.reduce((a, b) => (ORDER.indexOf(a) <= ORDER.indexOf(b) ? a : b), "verified" as Status);

/**
 * Status of a reported item: its obligations, the generated declarations it consists of
 * (any error in one of them, even where `#print axioms` looks clean, means it did not
 * elaborate), the items it uses (`broken`: one of them has a declaration that did not
 * elaborate — it may be missing, or another declaration of that name may stand in for it,
 * which `#print axioms` cannot show), then the axioms of its main declarations.
 */
function itemStatus(v: Verdict, it: Item, trustedAxioms: Set<string>, broken: boolean): Status {
  const ids = new Set(it.obs);
  if (v.failed.some((f) => ids.has(f.ob.id))) return "incomplete";
  const decl = [...v.declErrors.keys()].some(it.owns) || v.sorries.some((s) => !!s.decl && it.owns(s.decl));
  if (decl || broken) return "incomplete";
  const sts = it.axiomNames.map((q) => classify(v.axioms.get(q), it.own, trustedAxioms, v.assumedOutside.get(q)));
  // obligations Lean did not finish although their file was elaborated
  if (v.unchecked.some((u) => ids.has(u.id)) && !sts.includes("unchecked")) return "incomplete";
  return worst(sts);
}

/** A reported item as the report sees it (see `items`). */
interface Item {
  key: string;
  /** the TypeScript name (`App.certificate` for a certificate) and source file, for messages */
  name: string;
  file: string;
  module: string;
  /** the obligations its status depends on; `ownObs`: those generated for it (not for a part reported on its own) */
  obs: number[];
  ownObs: number[];
  refs: string[];
  /** whether a generated declaration (by full Lean name) is part of the item */
  owns: (lean: string) => boolean;
  /** the declarations whose axioms make up its status */
  axiomNames: string[];
  /** its own namespace (for its own @trusted axioms) */
  own: string;
}

function items(tr: TranslateResult, root: string): { comps: Item[]; certs: Item[]; fns: Item[]; consts: Item[] } {
  const out = { comps: [] as Item[], certs: [] as Item[], fns: [] as Item[], consts: [] as Item[] };
  for (const mr of tr.modules) {
    const file = relp(root, mr.tsFile);
    for (const c of mr.components) {
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${c.ns}.${s}`));
      out.comps.push({ key: c.ns, name: c.name, file, module: mr.ns, obs: c.obs, ownObs: c.obs, refs: c.refs, owns: (q) => q.startsWith(c.ns + ".") && !root.has(q), axiomNames: [`${c.ns}.component`], own: c.ns });
    }
    for (const c of mr.certificates) {
      const base = c.qname.replace(/\.certificate$/, "");
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${base}.${s}`));
      // (its obligations include its root component's, which belong to the component)
      const comp = new Set(mr.components.find((x) => x.ns === base)?.obs ?? []);
      out.certs.push({ key: c.qname, name: `${c.name}.certificate`, file, module: mr.ns, obs: c.obs, ownObs: c.obs.filter((o) => !comp.has(o)), refs: c.refs, owns: (q) => root.has(q), axiomNames: [c.qname], own: base });
    }
    for (const f of mr.functions) {
      // a function is as verified as its definition and all its postcondition theorems
      const names = new Set([f.qname, ...f.posts]);
      out.fns.push({ key: f.qname, name: f.name, file, module: mr.ns, obs: f.obs, ownObs: f.obs, refs: f.refs, owns: (q) => names.has(q), axiomNames: [...names], own: f.qname });
    }
    for (const c of mr.constants) {
      const names = new Set([c.qname, ...c.facts]);
      out.consts.push({ key: c.qname, name: c.name, file, module: mr.ns, obs: c.obs, ownObs: c.obs, refs: c.refs, owns: (q) => names.has(q), axiomNames: [...names], own: c.qname });
    }
  }
  return out;
}

/**
 * For every item: the broken declaration its dependency cone contains, if any. A generated
 * declaration that did not elaborate (`brokenDecls`) breaks its item. When Lean nevertheless
 * reports axioms without `sorryAx` for its name, another declaration of that name (e.g. from
 * a user proof) stands in for it: then it also breaks every item that uses that item,
 * directly or not, since those were checked against something that is not the translation
 * of the source (a missing declaration breaks its users by their own errors; one added with
 * `sorryAx` shows in their axioms). A broken declaration that belongs to no item (a type, …)
 * breaks its whole module and the modules importing it.
 */
function brokenCones(tr: TranslateResult, v: Verdict, all: Item[]): Map<string, string> {
  // (a module the kernel re-check did not certify: its reason as it stands)
  const why = (b: Verdict["brokenDecls"][number]) =>
    b.error.startsWith("the kernel re-check") ? b.error.slice(0, 200) : `${b.name ?? `the command at ${b.file}`} did not elaborate (${b.error.slice(0, 120)})`;
  const own = new Map<string, string>();
  /** broken items whose breakage dependents cannot see in their axioms */
  const hidden = new Map<string, string>();
  const brokenMods = new Map<string, string>();
  const modOf = (file: string) => "VTS." + file.split(/[\\/]/).slice(1, -1).join(".");
  for (const b of v.brokenDecls) {
    // (a failing `#print axioms` / `#vreact_assumed` defines nothing: its constant is missing,
    // see above, or its item lacks the report and is not checked)
    if (b.kind === "#print" || b.kind === "#vreact_assumed") continue;
    const it = b.name ? all.find((x) => x.owns(b.name!)) : undefined;
    if (it) {
      if (!own.has(it.key)) own.set(it.key, why(b));
      // (a part without its own report, e.g. a component's render: the item's reports)
      const reports = it.axiomNames.map((q) => v.axioms.get(q));
      const ax = v.axioms.get(b.name!) ?? (reports.every((r) => r !== undefined) ? reports.flat() : undefined);
      if (ax && !ax.includes("sorryAx") && !hidden.has(it.key)) hidden.set(it.key, why(b));
    } else if (!brokenMods.has(modOf(b.file))) brokenMods.set(modOf(b.file), why(b));
  }
  // modules importing a broken module are broken
  let grew = true;
  while (grew) {
    grew = false;
    for (const mr of tr.modules) {
      const up = mr.imports.find((i) => brokenMods.has(i));
      if (up && !brokenMods.has(mr.ns)) brokenMods.set(mr.ns, brokenMods.get(up)!), (grew = true);
    }
  }
  for (const it of all) {
    const m = brokenMods.get(it.module);
    if (m === undefined) continue;
    if (!own.has(it.key)) own.set(it.key, m);
    if (!hidden.has(it.key)) hidden.set(it.key, m);
  }
  const byKey = new Map(all.map((x) => [x.key, x]));
  const out = new Map<string, string>();
  for (const it of all) {
    const seen = new Set<string>([it.key]);
    const go = (k: string): string | undefined => {
      if (seen.has(k)) return undefined;
      seen.add(k);
      return hidden.get(k) ?? (byKey.get(k)?.refs ?? []).map(go).find((x) => x !== undefined);
    };
    const w = own.get(it.key) ?? it.refs.map(go).find((x) => x !== undefined);
    if (w !== undefined) out.set(it.key, w);
  }
  return out;
}

/** The axioms the translator emits for @trusted functions and components. */
function trustedAxiomsOf(tr: TranslateResult): Set<string> {
  const out = new Set<string>();
  for (const mr of tr.modules) {
    for (const f of mr.functions) if (f.trusted) [f.qname, ...f.posts].forEach((q) => out.add(q));
    for (const c of mr.components) if (c.trusted) ["init_inv", "stable", "renderTrusted"].forEach((s) => out.add(`${c.ns}.${s}`));
  }
  return out;
}

export interface Report {
  ok: boolean;
  verdict: "verified" | "verified-modulo-trusted" | "incomplete" | "not-verified";
  stage: "typescript" | "translation" | "lean";
  obligations: { total: number; proved: number; failed: number; unchecked: number };
  /**
   * `reason`: why an INCOMPLETE / UNCHECKED item is not verified (its own failure, or which
   * dependency failed), and what a TRUSTED item that is not @trusted itself relies on (axioms
   * of user proofs)
   */
  components: { name: string; file: string; status: Status; axioms: string[]; reason?: string }[];
  functions: { name: string; file: string; status: Status; reason?: string }[];
  constants: { name: string; file: string; status: Status; reason?: string }[];
  certificates: { name: string; theorem: string; status: Status; axioms: string[]; reason?: string }[];
  failures: { where: string; kind: string; desc: string; lean: string; leanFull: string }[];
  /** obligations that were not (completely) checked, with the reason */
  notChecked: { where: string; kind: string; desc: string; reason: string }[];
  /** `sorry` left in generated Lean or user proofs (`hole()`, pending contracts, …) */
  sorries: string[];
  /**
   * declarations outside the generated code (user proofs) that use `VReact.assumed`, the axiom
   * behind `assume(…)`, directly and that a reported item relies on (each such item is TRUSTED)
   */
  assumedByProofs: string[];
  errors: string[];
}

/** The reason of an item that is incomplete only because of a hole() or sorry in its own code. */
const HOLE = "pending: it has a hole() / sorry";

export const CAUSE_LABEL: Record<ErrorCause, string> = {
  build: "Lean build error (imports, lakefile, missing or clashing files)",
  proof: "user proof",
  timeout: "timeout",
  "follow-on": "follow-on error (a declaration above failed)",
  internal: "internal (generated Lean)",
};

function errorWhere(i: LeanMessage): string {
  const pos = i.line ? `:${i.line}:${i.col}` : "";
  // (a generated module that a user proof broke: named as it is)
  if (i.cause === "proof") return !i.file ? "user proofs" : /^Proofs[\\/]/.test(i.file) ? `user proof proofs/${i.file.replace(/^Proofs[\\/]/, "")}${pos}` : `user proof (it affects ${i.file}${pos})`;
  return `${CAUSE_LABEL[i.cause ?? "internal"]}${i.file ? " " + i.file + pos : ""}${i.decl ? ` (in ${i.decl})` : ""}`;
}

export function verify(cfg: Config, opts: { json?: boolean; quiet?: boolean; full?: boolean } = {}): Report {
  const t0 = Date.now();
  const tr = translate(cfg);
  const report: Report = {
    ok: false,
    verdict: "not-verified",
    stage: "typescript",
    obligations: { total: tr.obligations.length, proved: 0, failed: 0, unchecked: 0 },
    components: [],
    functions: [],
    constants: [],
    certificates: [],
    failures: [],
    notChecked: [],
    sorries: [],
    assumedByProofs: [],
    errors: [],
  };
  if (!tr.ok) {
    report.stage = tr.tsDiagnostics.length ? "typescript" : "translation";
    report.errors = [...tr.tsDiagnostics, ...tr.errors.map((e: VtsError) => `${e.file ? relp(cfg.root, e.file) : "?"}:${e.line}:${e.col}: ${e.message}`)];
    if (!opts.json) printTranslationErrors(tr, cfg.root);
    return report;
  }
  editorFiles(cfg, !opts.json && !opts.quiet);
  if (!opts.json && !opts.quiet) console.log(C.d(`translated ${tr.modules.length} module(s), ${tr.obligations.length} proof obligation(s) → ${relp(cfg.root, cfg.outDir)}/ ; checking with Lean…`));
  const lk = runLake(cfg.outDir, cfg.leanLib);
  const { report: r, v } = reportFrom(cfg, tr, lk.messages);
  if (!opts.json) printReport(r, tr, v, cfg, Date.now() - t0, !!opts.full);
  return r;
}

/**
 * The report of a translated program from Lean's messages (`runLake`; exported so that the
 * regression suite can check the report against doctored Lean output).
 */
export function reportFrom(cfg: Config, tr: TranslateResult, messages: LeanMessage[]): { report: Report; v: Verdict } {
  const report: Report = {
    ok: false,
    verdict: "not-verified",
    stage: "lean",
    obligations: { total: tr.obligations.length, proved: 0, failed: 0, unchecked: 0 },
    components: [],
    functions: [],
    constants: [],
    certificates: [],
    failures: [],
    notChecked: [],
    sorries: [],
    assumedByProofs: [],
    errors: [],
  };
  const markers = findMarkers(cfg.outDir);
  const v: Verdict = judge(tr.obligations, messages, markers, cfg.outDir);
  // proofs by native evaluation: not a trusted assumption the report could name, an error
  const native = [...new Set([...v.axioms.values()].flat())].filter(isNativeAxiom);
  if (native.length) {
    v.internal.push({ severity: "error", file: "", line: 0, col: 0, cause: "proof", text: `a proof uses native evaluation (axiom${native.length > 1 ? "s" : ""} ${native.join(", ")}: native_decide, decide +native, bv_decide or Lean.ofReduceBool), which trusts Lean's compiler instead of its kernel; vreact does not accept such proofs` });
  }
  const its = items(tr, cfg.root);
  const all = [...its.comps, ...its.certs, ...its.fns, ...its.consts];
  const broken = brokenCones(tr, v, all);
  // an obligation of an item whose cone has a broken declaration is not about the translated code
  for (const it of all) {
    const w = broken.get(it.key);
    if (w === undefined) continue;
    const ids = new Set(it.ownObs);
    for (const ob of v.proved.filter((o) => ids.has(o.id))) {
      v.unchecked.push(ob);
      v.reasons.set(ob.id, `${w}: it is part of, or used by, this obligation's item, so the obligation is not about the translated code`);
    }
    v.proved = v.proved.filter((o) => !ids.has(o.id));
  }
  const byKey = new Map(all.map((x) => [x.key, x]));
  /** the item and the items it uses, directly or not (breadth-first: the closest first) */
  const cone = (it: Item): Item[] => {
    const out = [it];
    const seen = new Set([it.key]);
    for (let i = 0; i < out.length; i++)
      for (const r of out[i].refs) {
        const x = byKey.get(r);
        if (x && !seen.has(r)) seen.add(r), out.push(x);
      }
    return out;
  };
  /** what Lean reported wrong with an item itself */
  const ownTrouble = (it: Item): string | undefined => {
    const ids = new Set(it.ownObs);
    const nf = v.failed.filter((f) => ids.has(f.ob.id)).length;
    if (nf) return `${nf === 1 ? "an obligation" : `${nf} obligations`} of it failed`;
    const nu = v.unchecked.filter((u) => ids.has(u.id));
    if (nu.length) return `${nu.length === 1 ? "an obligation" : `${nu.length} obligations`} of it ${nu.length === 1 ? "was" : "were"} not checked: ${v.reasons.get(nu[0].id) ?? "not checked"}`;
    const de = [...v.declErrors].find(([q]) => it.owns(q));
    if (de) return `${de[0]} has an error (${de[1].split("\n")[0].slice(0, 100)})`;
    if (v.sorries.some((s) => !!s.decl && it.owns(s.decl))) return HOLE;
    return undefined;
  };
  const inProofs = (f: string) => /^Proofs[\\/]/.test(f);
  const proofTrouble = v.sorries.some((s) => inProofs(s.file)) || v.internal.some((i) => i.cause === "proof");
  // The obligations of an item count as proved only if its declarations were elaborated with
  // clean axioms: Lean reported the axioms of each, and `sorryAx` among them comes from a
  // reported failure, hole or broken declaration (of the item or one it uses) or from a user
  // proof. Otherwise Lean admitted something without saying why, and nothing in the item is
  // counted as proved.
  const troubled = new Set(all.filter((x) => ownTrouble(x) !== undefined || broken.has(x.key)).map((x) => x.key));
  for (const it of all) {
    const ids = new Set(it.ownObs);
    const mine = v.proved.filter((o) => ids.has(o.id));
    if (!mine.length) continue;
    const missing = it.axiomNames.find((q) => !v.axioms.has(q));
    const sorry = it.axiomNames.find((q) => v.axioms.get(q)?.includes("sorryAx"));
    const native = it.axiomNames.find((q) => v.axioms.get(q)?.some(isNativeAxiom));
    const why =
      missing !== undefined ? `Lean reported no axioms for ${missing}, so it may not have been added`
      : sorry !== undefined && !proofTrouble && !cone(it).some((x) => troubled.has(x.key)) ? `${sorry} depends on sorryAx, but Lean reported no failure or sorry it could come from`
      : native !== undefined ? `${native} depends on ${v.axioms.get(native)!.find(isNativeAxiom)}, an axiom of native evaluation (it trusts Lean's compiler instead of its kernel)`
      : undefined;
    if (why === undefined) continue;
    for (const ob of mine) {
      v.unchecked.push(ob);
      v.reasons.set(ob.id, `${why}: the obligation is not counted as proved`);
    }
    v.proved = v.proved.filter((o) => !ids.has(o.id));
  }
  /** why an INCOMPLETE or UNCHECKED item is not verified: its own trouble first, then the closest troubled item it uses */
  const reasonOf = (it: Item, st: Status): string | undefined => {
    if (st === "trusted") return trustReason(it);
    if (st !== "incomplete" && st !== "unchecked") return undefined;
    const own = ownTrouble(it);
    const dep = cone(it).slice(1).find((x) => ownTrouble(x) !== undefined);
    // (obligations that could not be checked because they depend on a failure elsewhere: name it)
    const ids = new Set(it.ownObs);
    const onlyBlocked = !v.failed.some((f) => ids.has(f.ob.id)) && v.unchecked.some((u) => ids.has(u.id)) && v.unchecked.every((u) => !ids.has(u.id) || v.blocked.has(u.id));
    if (own !== undefined && !(dep && onlyBlocked)) return own;
    const b = broken.get(it.key);
    if (b !== undefined && !dep) return b;
    if (dep) return `it uses ${dep.name}${dep.file !== it.file ? ` (${dep.file})` : ""}, which is not verified: ${ownTrouble(dep)}${onlyBlocked ? " (so some of its own obligations could not be checked)" : ""}`;
    if (own !== undefined) return own;
    const missing = it.axiomNames.find((q) => !v.axioms.has(q));
    if (missing !== undefined) return `Lean reported no axioms for ${missing} (its module was not checked to the end)`;
    const nat = it.axiomNames.flatMap((q) => v.axioms.get(q) ?? []).find(isNativeAxiom);
    if (nat !== undefined) return `its proof uses ${nat}, an axiom of native evaluation (native_decide, decide +native, bv_decide): it trusts Lean's compiler instead of its kernel`;
    const noAudit = it.axiomNames.find((q) => v.axioms.get(q)?.some((a) => ASSUMED.has(a)) && !v.assumedOutside.has(q));
    if (noAudit !== undefined) return `${noAudit} relies on VReact.assumed, but Lean printed no \`#vreact_assumed\` report for it: whether that is only the program's assume(…) facts was not checked`;
    if (it.axiomNames.some((q) => v.axioms.get(q)?.includes("sorryAx"))) return proofTrouble ? "its proof depends on sorry (sorryAx), e.g. from a user proof that failed or uses sorry" : "its proof depends on sorry (sorryAx)";
    return undefined;
  };
  /**
   * What a TRUSTED item that is not @trusted itself relies on: user-proof declarations that use
   * `VReact.assumed` directly, and axioms declared outside the translation.
   */
  const trustReason = (it: Item): string | undefined => {
    const axs = it.axiomNames.flatMap((q) => v.axioms.get(q) ?? []);
    // (an @trusted declaration is TRUSTED for its own sake)
    if (axs.some((a) => trustedAxioms.has(a) && (a === it.own || a.startsWith(it.own + ".")))) return undefined;
    const foreign = [...new Set(axs.filter((a) => !STD_AXIOMS.has(a) && !ASSUMED.has(a) && a !== "sorryAx" && !trustedAxioms.has(a) && !isNativeAxiom(a)))];
    const viaProofs = [...new Set(it.axiomNames.flatMap((q) => (v.axioms.get(q)?.some((a) => ASSUMED.has(a)) ? (v.assumedOutside.get(q) ?? []) : [])))];
    const parts: string[] = [];
    if (viaProofs.length) parts.push(`it relies on ${viaProofs.join(", ")} (outside the generated code: a user proof), which ${viaProofs.length === 1 ? "uses" : "use"} VReact.assumed — the axiom behind assume(…) — directly: an unproved fact, i.e. an axiom of the proof file, not an assume(…) of the program`);
    if (foreign.length) parts.push(`it relies on the ${foreign.length === 1 ? "axiom" : "axioms"} ${foreign.join(", ")}, declared outside the translation (in a user proof)`);
    return parts.length ? parts.join("; ") : undefined;
  };
  const withReason = (it: Item, st: Status) => {
    const r = reasonOf(it, st);
    return r === undefined ? {} : { reason: r };
  };
  const trustedAxioms = trustedAxiomsOf(tr);
  report.obligations = { total: tr.obligations.length, proved: v.proved.length, failed: v.failed.length, unchecked: v.unchecked.length };
  for (const f of v.failed) report.failures.push({ where: f.ob.where, kind: f.ob.kind, desc: f.ob.desc, lean: summarizeLeanError(f.message), leanFull: f.message });
  for (const u of v.unchecked) report.notChecked.push({ where: u.where, kind: u.kind, desc: u.desc, reason: v.reasons.get(u.id) ?? "not checked" });
  for (const i of v.internal) report.errors.push(`${errorWhere(i)}: ${i.text.split("\n").slice(0, 12).join("\n")}`);
  for (const s of v.sorries) report.sorries.push(`${s.file}:${s.line}:${s.col}${s.decl ? ` (${s.decl})` : ""}`);
  report.assumedByProofs = [...new Set(all.flatMap((it) => it.axiomNames.flatMap((q) => (v.axioms.get(q)?.some((a) => ASSUMED.has(a)) ? (v.assumedOutside.get(q) ?? []) : []))))].sort();
  const status = (it: Item) => itemStatus(v, it, trustedAxioms, broken.has(it.key));
  const k = { comp: 0, cert: 0, fn: 0, cst: 0 };
  for (const mr of tr.modules) {
    for (const c of mr.components) {
      const it = its.comps[k.comp++];
      const st = c.trusted ? "trusted" : status(it);
      report.components.push({ name: c.name, file: `${relp(cfg.root, mr.tsFile)}:${c.line}`, status: st, axioms: v.axioms.get(`${c.ns}.component`) ?? [], ...withReason(it, st) });
    }
    for (const c of mr.certificates) {
      const it = its.certs[k.cert++];
      const st = status(it);
      report.certificates.push({ name: c.name, theorem: c.qname, status: st, axioms: v.axioms.get(c.qname) ?? [], ...withReason(it, st) });
    }
    for (const f of mr.functions) {
      const it = its.fns[k.fn++];
      const st = f.trusted ? "trusted" : status(it);
      report.functions.push({ name: f.name, file: relp(cfg.root, mr.tsFile), status: st, ...withReason(it, st) });
    }
    for (const c of mr.constants) {
      const it = its.consts[k.cst++];
      const st = status(it);
      report.constants.push({ name: c.name, file: relp(cfg.root, mr.tsFile), status: st, ...withReason(it, st) });
    }
  }
  const statuses = [...report.components, ...report.functions, ...report.constants, ...report.certificates].map((x) => x.status);
  report.ok = v.failed.length === 0 && v.internal.length === 0 && v.unchecked.length === 0 && v.sorries.length === 0 && statuses.every((s) => s === "verified");
  report.verdict =
    v.failed.length || v.internal.length ? "not-verified"
    : statuses.some((s) => s === "incomplete" || s === "unchecked") || v.unchecked.length || v.sorries.length ? "incomplete"
    : statuses.some((s) => s === "trusted" || s === "assumes" || s === "relative") ? "verified-modulo-trusted"
    : "verified";
  return { report, v };
}

function printReport(r: Report, tr: TranslateResult, v: Verdict, cfg: Config, ms: number, full: boolean) {
  const badge = (s: Status) =>
    s === "verified" ? C.g("VERIFIED") : s === "relative" ? C.y("VERIFIED*") : s === "trusted" ? C.y("TRUSTED") : s === "assumes" ? C.y("ASSUMES") : s === "unchecked" ? C.y("UNCHECKED") : C.r("INCOMPLETE");
  // per-file obligation tallies
  const byFile = new Map<string, { total: number; failed: number; unchecked: number }>();
  for (const ob of tr.obligations) {
    const f = ob.where.split(":")[0];
    const e = byFile.get(f) ?? { total: 0, failed: 0, unchecked: 0 };
    e.total++;
    byFile.set(f, e);
  }
  for (const f of v.failed) byFile.get(f.ob.where.split(":")[0])!.failed++;
  for (const u of v.unchecked) byFile.get(u.where.split(":")[0])!.unchecked++;
  // why an item is INCOMPLETE / UNCHECKED (its own failure, or the dependency that failed)
  const why = (x: { reason?: string }) => (x.reason ? "\n" + C.d(`      ↳ ${x.reason}`) : "");
  console.log("");
  console.log(C.b("Components"));
  for (const c of r.components) console.log(`  ${badge(c.status).padEnd(18)} ${c.name.padEnd(22)} ${C.d(c.file)}${why(c)}`);
  if (r.functions.length) {
    console.log(C.b("Functions"));
    for (const f of r.functions) console.log(`  ${badge(f.status).padEnd(18)} ${f.name}${why(f)}`);
  }
  // constants are listed only when something is wrong with them (most are plain data)
  const badConsts = r.constants.filter((c) => c.status !== "verified");
  if (badConsts.length) {
    console.log(C.b("Constants"));
    for (const c of badConsts) console.log(`  ${badge(c.status).padEnd(18)} ${c.name}${why(c)}`);
  }
  if (r.certificates.length) {
    console.log(C.b("App certificates (VReact.run_allInv instantiated)"));
    for (const c of r.certificates) console.log(`  ${badge(c.status).padEnd(18)} ${c.theorem}  ${C.d("axioms: " + (c.axioms.join(", ") || "none"))}${why(c)}`);
  }
  console.log(C.b("Obligations by file"));
  for (const [f, e] of byFile) {
    const mark = e.failed ? C.r("✗") : e.unchecked ? C.y("?") : C.g("✓");
    const note = e.unchecked ? C.y(`  (${e.unchecked} not checked)`) : "";
    console.log(`  ${mark} ${f.padEnd(40)} ${e.total - e.failed - e.unchecked}/${e.total}${note}`);
  }
  if (v.failed.length) {
    console.log(C.b("\nFailed obligations"));
    const sorted = [...v.failed].sort((a, b) => a.ob.where.localeCompare(b.ob.where, undefined, { numeric: true }));
    for (const f of sorted) {
      console.log(`${C.r("✗")} ${f.ob.where}  [${f.ob.kind}] ${f.ob.desc}`);
      const text = full ? f.message : summarizeLeanError(f.message, 18);
      console.log(C.d(text.split("\n").map((l) => "    │ " + l).join("\n")));
    }
  }
  if (v.unchecked.length) {
    console.log(C.y(`\n${v.unchecked.length} obligation(s) not checked:`));
    // one line per reason (the reasons name the file or declaration that failed)
    const byWhy = new Map<string, string[]>();
    for (const u of v.unchecked) {
      const why = v.reasons.get(u.id) ?? "not checked";
      byWhy.set(why, [...(byWhy.get(why) ?? []), `${u.where} [${u.kind}]`]);
    }
    for (const [why, wheres] of byWhy) console.log(C.y(`  ${wheres.slice(0, 4).join(", ")}${wheres.length > 4 ? `, … (${wheres.length})` : ""}: ${why}`));
  }
  if (v.internal.length) {
    const sections: [ErrorCause, string][] = [
      ["build", "Lean build errors (imports, lakefile, missing or clashing files) — fix these first:"],
      ["proof", "Errors in user proofs (proofs/*.lean):"],
      ["timeout", "Timeouts outside a single obligation (the declaration was not finished):"],
      ["internal", "Internal errors in generated Lean (translator bug or unsupported pattern):"],
      ["follow-on", "Follow-on errors (uses of a declaration that failed above):"],
    ];
    for (const [cause, title] of sections) {
      const msgs = v.internal.filter((i) => (i.cause ?? "internal") === cause);
      if (!msgs.length) continue;
      console.log(C.r(`\n${title}`));
      for (const i of msgs.slice(0, 8)) {
        const loc = cause === "proof" && /^Proofs[\\/]/.test(i.file) ? `proofs/${i.file.replace(/^Proofs[\\/]/, "")}:${i.line}:${i.col}` : cause === "proof" && !i.file ? "proofs" : i.file ? `${i.file}${i.line ? `:${i.line}:${i.col}` : ""}` : "lake";
        console.log(`  ${loc}${i.decl ? ` (in ${i.decl})` : ""}: ${i.text.split("\n").slice(0, 10).join("\n    ")}`);
      }
      if (msgs.length > 8) console.log(`  … ${msgs.length - 8} more (--json lists all)`);
    }
  }
  const o = r.obligations;
  const items = [...r.components, ...r.functions, ...r.constants];
  // TRUSTED items: @trusted ones (contracts assumed), and items whose proofs use an axiom from
  // outside the translation (declared in a user proof, or `VReact.assumed` used directly by a
  // user-proof declaration: an unproved fact of the proof file, not an assume(…) of the program;
  // these have a ↳ reason)
  const declaredTrusted = new Set(tr.modules.flatMap((mr) => [
    ...mr.functions.filter((f) => f.trusted).map((f) => `${relp(cfg.root, mr.tsFile)}#${f.name}`),
    ...mr.components.filter((c) => c.trusted).map((c) => `${relp(cfg.root, mr.tsFile)}:${c.line}#${c.name}`),
  ]));
  const trustedItems = items.filter((x) => x.status === "trusted");
  const trusted = trustedItems.filter((x) => declaredTrusted.has(`${x.file}#${x.name}`)).map((x) => x.name);
  const trustedByAxiom = trustedItems.filter((x) => !declaredTrusted.has(`${x.file}#${x.name}`)).map((x) => x.name);
  const assumes = items.filter((x) => x.status === "assumes").map((x) => x.name);
  const trustedAx = trustedAxiomsOf(tr);
  const foreign = [...new Set([...v.axioms.values()].flat())].filter((a) => !STD_AXIOMS.has(a) && !ASSUMED.has(a) && a !== "sorryAx" && !trustedAx.has(a) && !isNativeAxiom(a));
  const modulo = [
    trusted.length || items.some((x) => x.status === "relative") ? "@trusted declarations" : "",
    trustedByAxiom.length ? "axioms from outside the translation" : "",
    assumes.length ? "assume(…) facts" : "",
  ].filter(Boolean).join(" and ") || "@trusted declarations";
  const head =
    r.verdict === "verified" ? C.g("✔ VERIFIED")
    : r.verdict === "verified-modulo-trusted" ? C.y(`✔ VERIFIED modulo ${modulo}`)
    : r.verdict === "incomplete" ? C.y("◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)")
    : C.r("✗ NOT VERIFIED");
  // (only items with a hole() / sorry of their own: an item that is INCOMPLETE for another
  // reason shows that reason above)
  const holes = [...r.components, ...r.functions, ...r.constants].filter((x) => x.reason === HOLE).map((x) => x.name);
  if (trusted.length) console.log(C.y(`\ntrusted (not verified, contracts assumed): ${trusted.join(", ")}`));
  if (trustedByAxiom.length) console.log(C.y(`${trusted.length ? "" : "\n"}trusted (their proofs use axioms from outside the translation — declared in, or used directly by, user proofs; see ↳ above and below): ${trustedByAxiom.join(", ")}`));
  if (assumes.length) console.log(C.y(`${trusted.length || trustedByAxiom.length ? "" : "\n"}assumes (checked, but relies on unproved assume(…) facts): ${assumes.join(", ")}`));
  if (items.some((x) => x.status === "relative")) console.log(C.y(`VERIFIED* = all own obligations proved; relies on the contracts of the trusted declarations above`));
  if (foreign.length) console.log(C.y(`axioms from outside the translation (TRUSTED wherever used; declared in user proofs?): ${foreign.join(", ")}`));
  if (r.assumedByProofs.length) console.log(C.y(`user-proof declarations that use VReact.assumed (the axiom behind assume(…)) directly — unproved facts, TRUSTED wherever used (prove them, or state the fact with assume(…) in the program): ${r.assumedByProofs.join(", ")}`));
  if (holes.length && !r.failures.length) console.log(C.y(`pending (hole() / sorry): ${holes.join(", ")}`));
  else if (r.sorries.length && !r.failures.length) console.log(C.y(`pending (sorry in the generated Lean or proofs): ${r.sorries.join(", ")}`));
  console.log(
    `\n${head}  ${o.proved}/${o.total} obligations proved` +
      (o.failed ? `, ${o.failed} failed` : "") +
      (o.unchecked ? `, ${o.unchecked} unchecked` : "") +
      `; components: ${r.components.filter((c) => c.status === "verified").length}/${r.components.length} verified` +
      C.d(`  (${(ms / 1000).toFixed(1)}s)`),
  );
}

const USAGE = `usage:
  vreact verify    [--root DIR] [--json] [--full] [--quiet]
                                           translate to Lean, check every obligation, report
                                           (--full: complete Lean goals of failed obligations)
  vreact translate [--root DIR]            generate the Lean project only (.vreact/)
  vreact explain   [file.tsx] [--root DIR] print the generated Lean model
  vreact synth     <file.tsx> [--root DIR] [--write]
                                           synthesize hole() placeholders against the spec`;

/** A misuse of the command line: reported with the usage, never with a stack trace. */
export class UsageError extends Error {}

const COMMANDS: Record<string, { flags: string[]; files: "none" | "optional" | "one" }> = {
  verify: { flags: ["--json", "--quiet", "--full"], files: "none" },
  translate: { flags: [], files: "none" },
  explain: { flags: [], files: "optional" },
  synth: { flags: ["--write", "--json"], files: "one" },
};

async function main(argv: string[]) {
  const cmd = argv[0];
  if (cmd === undefined || cmd === "help" || cmd === "--help" || cmd === "-h") {
    console.log(USAGE);
    return;
  }
  const spec = Object.hasOwn(COMMANDS, cmd) ? COMMANDS[cmd] : undefined;
  if (!spec) throw new UsageError(`unknown command "${cmd}"`);
  // the command's flags, `--root DIR`, and its file arguments
  const flags = new Set<string>();
  const positional: string[] = [];
  let rootArg: string | undefined;
  for (let i = 1; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--root") {
      if (i + 1 >= argv.length || argv[i + 1].startsWith("-")) throw new UsageError("--root needs a directory: --root DIR");
      rootArg = argv[++i];
    } else if (a.startsWith("--root=")) {
      rootArg = a.slice("--root=".length);
      if (!rootArg) throw new UsageError("--root needs a directory: --root DIR");
    } else if (a.startsWith("-")) {
      if (!spec.flags.includes(a)) throw new UsageError(`unknown option ${a} for "vreact ${cmd}" (options: ${["--root DIR", ...spec.flags].join(", ")})`);
      flags.add(a);
    } else positional.push(a);
  }
  if (spec.files === "none" && positional.length) throw new UsageError(`"vreact ${cmd}" takes no file argument (got ${positional.join(" ")}); the project directory is --root DIR`);
  if (spec.files === "one" && positional.length !== 1) throw new UsageError(positional.length ? `"vreact ${cmd}" takes one file (got ${positional.join(" ")})` : `"vreact ${cmd}" needs a file: vreact ${cmd} <file.tsx>`);
  if (spec.files === "optional" && positional.length > 1) throw new UsageError(`"vreact ${cmd}" takes at most one file (got ${positional.join(" ")})`);
  const root = path.resolve(rootArg ?? process.cwd());
  if (!fs.existsSync(root) || !fs.statSync(root).isDirectory()) throw new UsageError(`--root ${rootArg ?? root}: not a directory`);
  const flag = (n: string) => flags.has(n);
  // (results are exit codes, never process.exit: a large report written to a pipe is flushed
  // only after this function has returned)
  switch (cmd) {
    case "verify": {
      const cfg = loadConfig(root);
      const r = verify(cfg, { json: flag("--json"), quiet: flag("--quiet"), full: flag("--full") });
      if (flag("--json")) console.log(JSON.stringify(r, null, 2));
      process.exitCode = r.ok ? 0 : 1;
      return;
    }
    case "translate": {
      const cfg = loadConfig(root);
      const tr = translate(cfg);
      if (!tr.ok) {
        printTranslationErrors(tr, root);
        process.exitCode = 1;
        return;
      }
      editorFiles(cfg, true);
      console.log(`wrote ${tr.modules.length} module(s), ${tr.obligations.length} obligation(s) to ${relp(root, cfg.outDir)}/`);
      return;
    }
    case "explain": {
      const cfg = loadConfig(root);
      const target = positional[0] ? path.resolve(root, positional[0]) : null;
      if (target && !cfg.files.includes(target)) {
        console.log(fs.existsSync(target) ? `✗ ${positional[0]} is not one of the project's VTS files (see "src"/"include"/"exclude" in vreact.json)` : `✗ ${positional[0]}: no such file`);
        process.exitCode = 1;
        return;
      }
      const tr = translate(cfg);
      if (!tr.ok) {
        printTranslationErrors(tr, root);
        process.exitCode = 1;
        return;
      }
      for (const m of tr.modules) {
        if (target && m.tsFile !== target) continue;
        for (const part of ["Defs", "Posts", "View"]) {
          const p = path.join(cfg.outDir, ...m.ns.split("."), `${part}.lean`);
          if (part === "Posts" && !fs.existsSync(p)) continue;
          console.log(C.b(`── ${path.relative(root, p)} ──`));
          console.log(fs.readFileSync(p, "utf8"));
        }
      }
      return;
    }
    case "synth": {
      const { synthCommand } = await import("./synth.ts");
      await synthCommand(root, positional, { write: flag("--write"), json: flag("--json") });
      return;
    }
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main(process.argv.slice(2)).catch((e: unknown) => {
    if (e instanceof UsageError) {
      console.error(`vreact: ${e.message}\n\n${USAGE}`);
      process.exitCode = 2;
      return;
    }
    // a problem of the project or the environment (no Lean, a bad vreact.json, a missing source
    // directory, …): its message; the stack trace only on request
    const err = e instanceof Error ? e : new Error(String(e));
    console.error(`vreact: ${err.message}${process.env.VREACT_DEBUG ? "\n" + err.stack : "\n(set VREACT_DEBUG=1 to see where it happened)"}`);
    process.exitCode = 2;
  });
}
