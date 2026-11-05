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

function classify(axioms: string[] | undefined, own?: string): Status {
  if (!axioms) return "unchecked";
  if (axioms.includes("sorryAx")) return "incomplete";
  const vts = axioms.filter((a) => a.startsWith("VTS."));
  const ownTrusted = vts.some((a) => !own || a.startsWith(own + "."));
  if (ownTrusted) return "trusted";
  if (axioms.some((a) => ASSUMED.has(a))) return "assumes";
  // only trusted *dependencies* (not the declaration's own namespace): verified relative to them
  if (vts.length) return "relative";
  if (axioms.every((a) => STD_AXIOMS.has(a))) return "verified";
  return "trusted";
}

const ORDER: Status[] = ["unchecked", "incomplete", "trusted", "assumes", "relative", "verified"];
const worst = (sts: Status[]) => sts.reduce((a, b) => (ORDER.indexOf(a) <= ORDER.indexOf(b) ? a : b), "verified" as Status);

/**
 * Status of a reported item: its obligations, the generated declarations it consists of
 * (any error in one of them, even where `#print axioms` looks clean, means it did not
 * elaborate), then the axioms of its main declarations.
 */
function itemStatus(v: Verdict, obs: number[], ownsDecl: (lean: string) => boolean, axiomNames: string[], own: string): Status {
  const ids = new Set(obs);
  if (v.failed.some((f) => ids.has(f.ob.id))) return "incomplete";
  const decl = [...v.declErrors.keys()].some(ownsDecl) || v.sorries.some((s) => !!s.decl && ownsDecl(s.decl));
  if (decl) return "incomplete";
  const sts = axiomNames.map((q) => classify(v.axioms.get(q), own));
  // obligations Lean did not finish although their file was elaborated
  if (v.unchecked.some((u) => ids.has(u.id)) && !sts.includes("unchecked")) return "incomplete";
  return worst(sts);
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
  report.stage = "lean";
  if (!opts.json && !opts.quiet) console.log(C.d(`translated ${tr.modules.length} module(s), ${tr.obligations.length} proof obligation(s) → ${relp(cfg.root, cfg.outDir)}/ ; checking with Lean…`));
  const lk = runLake(cfg.outDir);
  const markers = findMarkers(cfg.outDir);
  const v: Verdict = judge(tr.obligations, lk.messages, markers, cfg.outDir);
  report.obligations = { total: tr.obligations.length, proved: v.proved.length, failed: v.failed.length, unchecked: v.unchecked.length };
  for (const f of v.failed) report.failures.push({ where: f.ob.where, kind: f.ob.kind, desc: f.ob.desc, lean: summarizeLeanError(f.message), leanFull: f.message });
  for (const u of v.unchecked) report.notChecked.push({ where: u.where, kind: u.kind, desc: u.desc, reason: v.reasons.get(u.id) ?? "not checked" });
  for (const i of v.internal) report.errors.push(`${errorWhere(i)}: ${i.text.split("\n").slice(0, 12).join("\n")}`);
  for (const s of v.sorries) report.sorries.push(`${s.file}:${s.line}:${s.col}${s.decl ? ` (${s.decl})` : ""}`);
  for (const mr of tr.modules) {
    for (const c of mr.components) {
      const ax = v.axioms.get(`${c.ns}.component`);
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${c.ns}.${s}`));
      const owns = (q: string) => q.startsWith(c.ns + ".") && !root.has(q);
      report.components.push({ name: c.name, file: `${relp(cfg.root, mr.tsFile)}:${c.line}`, status: c.trusted ? "trusted" : itemStatus(v, c.obs, owns, [`${c.ns}.component`], c.ns), axioms: ax ?? [] });
    }
    for (const c of mr.certificates) {
      const ax = v.axioms.get(c.qname);
      const base = c.qname.replace(/\.certificate$/, "");
      const root = new Set(["root_pre", "element", "certificate"].map((s) => `${base}.${s}`));
      report.certificates.push({ name: c.name, theorem: c.qname, status: itemStatus(v, c.obs, (q) => root.has(q), [c.qname], base), axioms: ax ?? [] });
    }
    for (const f of mr.functions) {
      // a function is as verified as its definition and all its postcondition theorems
      const names = new Set([f.qname, ...f.posts]);
      report.functions.push({ name: f.name, file: relp(cfg.root, mr.tsFile), status: f.trusted ? "trusted" : itemStatus(v, f.obs, (q) => names.has(q), [...names], f.qname) });
    }
    for (const c of mr.constants) {
      const names = new Set([c.qname, ...c.facts]);
      report.constants.push({ name: c.name, file: relp(cfg.root, mr.tsFile), status: itemStatus(v, c.obs, (q) => names.has(q), [...names], c.qname) });
    }
  }
  const statuses = [...report.components, ...report.functions, ...report.constants, ...report.certificates].map((x) => x.status);
  report.ok = v.failed.length === 0 && v.internal.length === 0 && v.unchecked.length === 0 && v.sorries.length === 0 && statuses.every((s) => s === "verified");
  report.verdict =
    v.failed.length || v.internal.length ? "not-verified"
    : statuses.some((s) => s === "incomplete" || s === "unchecked") || v.unchecked.length || v.sorries.length ? "incomplete"
    : statuses.some((s) => s === "trusted" || s === "assumes" || s === "relative") ? "verified-modulo-trusted"
    : "verified";
  if (!opts.json) printReport(report, tr, v, cfg, Date.now() - t0, !!opts.full);
  return report;
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
