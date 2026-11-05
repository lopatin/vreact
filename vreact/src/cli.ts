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
import { runLake, findMarkers, judge, summarizeLeanError, type Verdict } from "./lean.ts";
import { VtsError } from "./util.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_LIB = path.resolve(here, "..", "lean");

interface ProjectConfig {
  src?: string;
  include?: string[];
  exclude?: string[];
  proofs?: string;
  out?: string;
}

export function loadConfig(root: string, only?: string[]): Config {
  const cfgFile = path.join(root, "vreact.json");
  const pc: ProjectConfig = fs.existsSync(cfgFile) ? JSON.parse(fs.readFileSync(cfgFile, "utf8")) : {};
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

function classify(axioms: string[] | undefined, own?: string): Status {
  if (!axioms) return "unchecked";
  if (axioms.includes("sorryAx")) return "incomplete";
  const vts = axioms.filter((a) => a.startsWith("VTS."));
  // only trusted *dependencies* (not the declaration's own namespace): verified relative to them
  if (vts.length && own && vts.every((a) => !a.startsWith(own + "."))) return "relative";
  if (vts.length) return "trusted";
  if (axioms.includes("VReact.assumed")) return "assumes";
  if (axioms.every((a) => STD_AXIOMS.has(a))) return "verified";
  return "trusted";
}

export interface Report {
  ok: boolean;
  verdict: "verified" | "verified-modulo-trusted" | "incomplete" | "not-verified";
  stage: "typescript" | "translation" | "lean";
  obligations: { total: number; proved: number; failed: number; unchecked: number };
  components: { name: string; file: string; status: Status; axioms: string[] }[];
  functions: { name: string; status: Status }[];
  certificates: { name: string; theorem: string; status: Status; axioms: string[] }[];
  failures: { where: string; kind: string; desc: string; lean: string; leanFull: string }[];
  errors: string[];
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
    certificates: [],
    failures: [],
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
  for (const i of v.internal) {
    const where = i.file.startsWith("Proofs/") ? `user proof proofs/${i.file.slice(7)}` : `internal (generated Lean) ${i.file}`;
    report.errors.push(`${where}:${i.line}:${i.col}: ${i.text.split("\n").slice(0, 12).join("\n")}`);
  }
  for (const mr of tr.modules) {
    for (const c of mr.components) {
      const ax = v.axioms.get(`${c.ns}.component`);
      report.components.push({ name: c.name, file: `${relp(cfg.root, mr.tsFile)}:${c.line}`, status: c.trusted ? "trusted" : classify(ax, c.ns), axioms: ax ?? [] });
    }
    for (const c of mr.certificates) {
      const ax = v.axioms.get(c.qname);
      report.certificates.push({ name: c.name, theorem: c.qname, status: classify(ax, c.qname.replace(/\.certificate$/, "")), axioms: ax ?? [] });
    }
    for (const f of mr.functions) {
      // a function is as verified as its definition and all its postcondition theorems
      const order: Status[] = ["unchecked", "incomplete", "trusted", "assumes", "relative", "verified"];
      const sts = [f.qname, ...f.posts].map((q) => classify(v.axioms.get(q), f.qname));
      const worst = sts.reduce((a, b) => (order.indexOf(a) <= order.indexOf(b) ? a : b), "verified" as Status);
      report.functions.push({ name: f.name, status: f.trusted ? "trusted" : worst });
    }
  }
  const statuses = [...report.components, ...report.functions, ...report.certificates].map((x) => x.status);
  report.ok = v.failed.length === 0 && v.internal.length === 0 && v.unchecked.length === 0 && statuses.every((s) => s === "verified");
  report.verdict =
    v.failed.length || v.internal.length ? "not-verified"
    : statuses.some((s) => s === "incomplete" || s === "unchecked") || v.unchecked.length ? "incomplete"
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
  if (r.certificates.length) {
    console.log(C.b("App certificates (VReact.run_allInv instantiated)"));
    for (const c of r.certificates) console.log(`  ${badge(c.status).padEnd(18)} ${c.theorem}  ${C.d("axioms: " + (c.axioms.join(", ") || "none"))}`);
  }
  console.log(C.b("Obligations by file"));
  for (const [f, e] of byFile) {
    const mark = e.failed ? C.r("✗") : e.unchecked ? C.y("?") : C.g("✓");
    const note = e.unchecked ? C.y(`  (${e.unchecked} not checked: a dependency failed)`) : "";
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
  if (v.unchecked.length) console.log(C.y(`\n${v.unchecked.length} obligation(s) not checked because a dependency failed to build.`));
  if (v.internal.length) {
    const user = v.internal.filter((i) => i.file.startsWith("Proofs/"));
    const gen = v.internal.filter((i) => !i.file.startsWith("Proofs/"));
    if (user.length) {
      console.log(C.r("\nErrors in user proofs (proofs/*.lean):"));
      for (const i of user.slice(0, 8)) console.log(`  proofs/${i.file.slice(7)}:${i.line}:${i.col}: ${i.text.split("\n").slice(0, 10).join("\n    ")}`);
    }
    if (gen.length) {
      console.log(C.r("\nInternal errors in generated Lean (translator bug or unsupported pattern):"));
      for (const i of gen.slice(0, 8)) console.log(`  ${i.file}:${i.line}:${i.col}: ${i.text.split("\n").slice(0, 10).join("\n    ")}`);
    }
  }
  const o = r.obligations;
  const head =
    r.verdict === "verified" ? C.g("✔ VERIFIED")
    : r.verdict === "verified-modulo-trusted" ? C.y("✔ VERIFIED modulo @trusted declarations")
    : r.verdict === "incomplete" ? C.y("◐ INCOMPLETE (holes / trusted stubs / unchecked parts remain)")
    : C.r("✗ NOT VERIFIED");
  const trusted = [...r.components, ...r.functions].filter((x) => x.status === "trusted").map((x) => x.name);
  const holes = r.functions.filter((x) => x.status === "incomplete").map((x) => x.name);
  if (trusted.length) console.log(C.y(`\ntrusted (not verified, contracts assumed): ${trusted.join(", ")}`));
  if ([...r.components, ...r.functions].some((x) => x.status === "relative")) console.log(C.y(`VERIFIED* = all own obligations proved; relies on the contracts of the trusted declarations above`));
  if (holes.length && !r.failures.length) console.log(C.y(`pending (hole() / sorry): ${holes.join(", ")}`));
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
