#!/usr/bin/env node
/**
 * vreact — formally verified React (VTS → Lean 4).
 *
 *   vreact verify  [--root DIR] [--json] [--quiet]   translate, check with Lean, report
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
  const pc: ProjectConfig = fs.existsSync(cfgFile) ? JSON.parse(fs.readFileSync(cfgFile, "utf8")) : {};
  if (pc.heartbeats !== undefined && !(Number.isInteger(pc.heartbeats) && pc.heartbeats >= 0)) throw new Error(`${cfgFile}: "heartbeats" must be a non-negative integer (thousands of heartbeats per obligation)`);
  const srcDir = path.resolve(root, pc.src ?? "src");
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
 * `trustedAxioms`: the axioms the translator emits for @trusted declarations; any other
 * axiom (outside Lean's standard ones and `VReact.assumed`, e.g. one declared in a user
 * proof, also in a `VTS.` namespace) makes the item TRUSTED, never VERIFIED*.
 */
function classify(axioms: string[] | undefined, own: string, trustedAxioms: Set<string>): Status {
  if (!axioms) return "unchecked";
  if (axioms.includes("sorryAx")) return "incomplete";
  const vts = axioms.filter((a) => trustedAxioms.has(a));
  if (vts.some((a) => a === own || a.startsWith(own + "."))) return "trusted";
  if (axioms.some((a) => !STD_AXIOMS.has(a) && !ASSUMED.has(a) && !trustedAxioms.has(a))) return "trusted";
  if (axioms.some((a) => ASSUMED.has(a))) return "assumes";
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
  const sts = it.axiomNames.map((q) => classify(v.axioms.get(q), it.own, trustedAxioms));
  // obligations Lean did not finish although their file was elaborated
  if (v.unchecked.some((u) => ids.has(u.id)) && !sts.includes("unchecked")) return "incomplete";
  return worst(sts);
}

/** A reported item as the report sees it (see `items`). */
interface Item {
  key: string;
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

function items(tr: TranslateResult): { comps: Item[]; certs: Item[]; fns: Item[]; consts: Item[] } {
  const out = { comps: [] as Item[], certs: [] as Item[], fns: [] as Item[], consts: [] as Item[] };
  for (const mr of tr.modules) {
    for (const c of mr.components) {
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${c.ns}.${s}`));
      out.comps.push({ key: c.ns, module: mr.ns, obs: c.obs, ownObs: c.obs, refs: c.refs, owns: (q) => q.startsWith(c.ns + ".") && !root.has(q), axiomNames: [`${c.ns}.component`], own: c.ns });
    }
    for (const c of mr.certificates) {
      const base = c.qname.replace(/\.certificate$/, "");
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${base}.${s}`));
      // (its obligations include its root component's, which belong to the component)
      const comp = new Set(mr.components.find((x) => x.ns === base)?.obs ?? []);
      out.certs.push({ key: c.qname, module: mr.ns, obs: c.obs, ownObs: c.obs.filter((o) => !comp.has(o)), refs: c.refs, owns: (q) => root.has(q), axiomNames: [c.qname], own: base });
    }
    for (const f of mr.functions) {
      // a function is as verified as its definition and all its postcondition theorems
      const names = new Set([f.qname, ...f.posts]);
      out.fns.push({ key: f.qname, module: mr.ns, obs: f.obs, ownObs: f.obs, refs: f.refs, owns: (q) => names.has(q), axiomNames: [...names], own: f.qname });
    }
    for (const c of mr.constants) {
      const names = new Set([c.qname, ...c.facts]);
      out.consts.push({ key: c.qname, module: mr.ns, obs: c.obs, ownObs: c.obs, refs: c.refs, owns: (q) => names.has(q), axiomNames: [...names], own: c.qname });
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
  const why = (b: Verdict["brokenDecls"][number]) => `${b.name ?? `the command at ${b.file}`} did not elaborate (${b.error.slice(0, 120)})`;
  const own = new Map<string, string>();
  /** broken items whose breakage dependents cannot see in their axioms */
  const hidden = new Map<string, string>();
  const brokenMods = new Map<string, string>();
  const modOf = (file: string) => "VTS." + file.split(/[\\/]/).slice(1, -1).join(".");
  for (const b of v.brokenDecls) {
    // (a failing `#print axioms` defines nothing: its constant is missing, see above)
    if (b.kind === "#print") continue;
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
  components: { name: string; file: string; status: Status; axioms: string[] }[];
  functions: { name: string; file: string; status: Status }[];
  constants: { name: string; file: string; status: Status }[];
  certificates: { name: string; theorem: string; status: Status; axioms: string[] }[];
  failures: { where: string; kind: string; desc: string; lean: string; leanFull: string }[];
  /** obligations that were not (completely) checked, with the reason */
  notChecked: { where: string; kind: string; desc: string; reason: string }[];
  /** `sorry` left in generated Lean or user proofs (`hole()`, pending contracts, …) */
  sorries: string[];
  errors: string[];
}

export const CAUSE_LABEL: Record<ErrorCause, string> = {
  build: "Lean build error (imports, lakefile, missing or clashing files)",
  proof: "user proof",
  timeout: "timeout",
  "follow-on": "follow-on error (a declaration above failed)",
  internal: "internal (generated Lean)",
};

function errorWhere(i: LeanMessage): string {
  const pos = i.line ? `:${i.line}:${i.col}` : "";
  if (i.cause === "proof") return `user proof proofs/${i.file.replace(/^Proofs[\\/]/, "")}${pos}`;
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
    errors: [],
  };
  if (!tr.ok) {
    report.stage = tr.tsDiagnostics.length ? "typescript" : "translation";
    report.errors = [...tr.tsDiagnostics, ...tr.errors.map((e: VtsError) => `${e.file ? relp(cfg.root, e.file) : "?"}:${e.line}:${e.col}: ${e.message}`)];
    if (!opts.json) printTranslationErrors(tr, cfg.root);
    return report;
  }
  if (!opts.json && !opts.quiet) console.log(C.d(`translated ${tr.modules.length} module(s), ${tr.obligations.length} proof obligation(s) → ${relp(cfg.root, cfg.outDir)}/ ; checking with Lean…`));
  const lk = runLake(cfg.outDir);
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
    errors: [],
  };
  const markers = findMarkers(cfg.outDir);
  const v: Verdict = judge(tr.obligations, messages, markers, cfg.outDir);
  const its = items(tr);
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
  const trustedAxioms = trustedAxiomsOf(tr);
  report.obligations = { total: tr.obligations.length, proved: v.proved.length, failed: v.failed.length, unchecked: v.unchecked.length };
  for (const f of v.failed) report.failures.push({ where: f.ob.where, kind: f.ob.kind, desc: f.ob.desc, lean: summarizeLeanError(f.message), leanFull: f.message });
  for (const u of v.unchecked) report.notChecked.push({ where: u.where, kind: u.kind, desc: u.desc, reason: v.reasons.get(u.id) ?? "not checked" });
  for (const i of v.internal) report.errors.push(`${errorWhere(i)}: ${i.text.split("\n").slice(0, 12).join("\n")}`);
  for (const s of v.sorries) report.sorries.push(`${s.file}:${s.line}:${s.col}${s.decl ? ` (${s.decl})` : ""}`);
  const status = (it: Item) => itemStatus(v, it, trustedAxioms, broken.has(it.key));
  const k = { comp: 0, cert: 0, fn: 0, cst: 0 };
  for (const mr of tr.modules) {
    for (const c of mr.components) {
      const it = its.comps[k.comp++];
      report.components.push({ name: c.name, file: `${relp(cfg.root, mr.tsFile)}:${c.line}`, status: c.trusted ? "trusted" : status(it), axioms: v.axioms.get(`${c.ns}.component`) ?? [] });
    }
    for (const c of mr.certificates) {
      const it = its.certs[k.cert++];
      report.certificates.push({ name: c.name, theorem: c.qname, status: status(it), axioms: v.axioms.get(c.qname) ?? [] });
    }
    for (const f of mr.functions) {
      const it = its.fns[k.fn++];
      report.functions.push({ name: f.name, file: relp(cfg.root, mr.tsFile), status: f.trusted ? "trusted" : status(it) });
    }
    for (const c of mr.constants) {
      const it = its.consts[k.cst++];
      report.constants.push({ name: c.name, file: relp(cfg.root, mr.tsFile), status: status(it) });
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
  console.log("");
  console.log(C.b("Components"));
  for (const c of r.components) console.log(`  ${badge(c.status).padEnd(18)} ${c.name.padEnd(22)} ${C.d(c.file)}`);
  if (r.functions.length) {
    console.log(C.b("Functions"));
    for (const f of r.functions) console.log(`  ${badge(f.status).padEnd(18)} ${f.name}`);
  }
  // constants are listed only when something is wrong with them (most are plain data)
  const badConsts = r.constants.filter((c) => c.status !== "verified");
  if (badConsts.length) {
    console.log(C.b("Constants"));
    for (const c of badConsts) console.log(`  ${badge(c.status).padEnd(18)} ${c.name}`);
  }
  if (r.certificates.length) {
    console.log(C.b("App certificates (VReact.run_allInv instantiated)"));
    for (const c of r.certificates) console.log(`  ${badge(c.status).padEnd(18)} ${c.theorem}  ${C.d("axioms: " + (c.axioms.join(", ") || "none"))}`);
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
      byWhy.set(why, [...(byWhy.get(why) ?? []), u.where]);
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
        const loc = cause === "proof" ? `proofs/${i.file.replace(/^Proofs[\\/]/, "")}:${i.line}:${i.col}` : i.file ? `${i.file}${i.line ? `:${i.line}:${i.col}` : ""}` : "lake";
        console.log(`  ${loc}${i.decl ? ` (in ${i.decl})` : ""}: ${i.text.split("\n").slice(0, 10).join("\n    ")}`);
      }
      if (msgs.length > 8) console.log(`  … ${msgs.length - 8} more (--json lists all)`);
    }
  }
  const o = r.obligations;
  const items = [...r.components, ...r.functions, ...r.constants];
  const trusted = items.filter((x) => x.status === "trusted").map((x) => x.name);
  const assumes = items.filter((x) => x.status === "assumes").map((x) => x.name);
  const modulo = [trusted.length ? "@trusted declarations" : "", assumes.length ? "assume(…) facts" : ""].filter(Boolean).join(" and ") || "@trusted declarations";
  const head =
    r.verdict === "verified" ? C.g("✔ VERIFIED")
    : r.verdict === "verified-modulo-trusted" ? C.y(`✔ VERIFIED modulo ${modulo}`)
    : r.verdict === "incomplete" ? C.y("◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)")
    : C.r("✗ NOT VERIFIED");
  const holes = [...r.functions, ...r.constants].filter((x) => x.status === "incomplete").map((x) => x.name);
  if (trusted.length) console.log(C.y(`\ntrusted (not verified, contracts assumed): ${trusted.join(", ")}`));
  if (assumes.length) console.log(C.y(`${trusted.length ? "" : "\n"}assumes (checked, but relies on unproved assume(…) facts): ${assumes.join(", ")}`));
  if (items.some((x) => x.status === "relative")) console.log(C.y(`VERIFIED* = all own obligations proved; relies on the contracts of the trusted declarations above`));
  const trustedAx = trustedAxiomsOf(tr);
  const foreign = [...new Set([...v.axioms.values()].flat())].filter((a) => !STD_AXIOMS.has(a) && !ASSUMED.has(a) && a !== "sorryAx" && !trustedAx.has(a));
  if (foreign.length) console.log(C.y(`axioms from outside the translation (TRUSTED wherever used; declared in user proofs?): ${foreign.join(", ")}`));
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

async function main() {
  const argv = process.argv.slice(2);
  const cmd = argv[0];
  const flag = (n: string) => argv.includes(n);
  const opt = (n: string) => {
    const i = argv.indexOf(n);
    return i >= 0 ? argv[i + 1] : undefined;
  };
  const root = path.resolve(opt("--root") ?? process.cwd());
  const positional = argv.slice(1).filter((a, i, all) => !a.startsWith("--") && !(i > 0 && ["--root"].includes(all[i - 1])));
  switch (cmd) {
    case "verify": {
      const cfg = loadConfig(root);
      const r = verify(cfg, { json: flag("--json"), quiet: flag("--quiet"), full: flag("--full") });
      if (flag("--json")) console.log(JSON.stringify(r, null, 2));
      process.exit(r.ok ? 0 : 1);
    }
    case "translate": {
      const cfg = loadConfig(root);
      const tr = translate(cfg);
      if (!tr.ok) {
        printTranslationErrors(tr, root);
        process.exit(1);
      }
      console.log(`wrote ${tr.modules.length} module(s), ${tr.obligations.length} obligation(s) to ${relp(root, cfg.outDir)}/`);
      return;
    }
    case "explain": {
      const cfg = loadConfig(root);
      const tr = translate(cfg);
      if (!tr.ok) {
        printTranslationErrors(tr, root);
        process.exit(1);
      }
      const target = positional[0] ? path.resolve(root, positional[0]) : null;
      for (const m of tr.modules) {
        if (target && m.tsFile !== target) continue;
        for (const part of ["Defs", "View"]) {
          const p = path.join(cfg.outDir, ...m.ns.split("."), `${part}.lean`);
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
    default:
      console.log(`usage:
  vreact verify    [--root DIR] [--json] [--full]  translate to Lean, check every obligation, report
                                           (--full: complete Lean goals of failed obligations)
  vreact translate [--root DIR]            generate the Lean project only (.vreact/)
  vreact explain   [file.tsx] [--root DIR] print the generated Lean model
  vreact synth     <file.tsx> [--write]    synthesize hole() placeholders against the spec`);
      process.exit(cmd ? 1 : 0);
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
