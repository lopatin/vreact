/**
 * Regression suite: every case file starts with
 *   // expect: verified | fail <kind…> | reject <message substring> | status
 * `verified`/`fail`/`status` cases are checked together in one Lean build; `reject` cases
 * must be refused by the translator with the given message. Tokens `key=value` add
 * report checks (see `checkReport`): `Name=<status>` for a component/function/constant of
 * the case, `verdict=…`, `proved=N`, `unchecked=N`, `errors=<cause>`, `failtext=<word>`,
 * `why.Name=<text>` (the item's reported reason mentions the text; `~` stands for a space).
 * A directory `cases/<Name>/` is a multi-file case with its own project: its .ts/.tsx files
 * and subdirectories go to src/, `proofs/` and `vreact.json` are copied, `tsconfig.json` replaces the default
 * one (a file `NO_TSCONFIG` means none); the header of its first source file applies.
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { loadConfig, verify, CAUSE_LABEL, type Report } from "../src/cli.ts";
import { translate } from "../src/module.ts";
import { parseMessages, judge, findMarkers, leanDecls } from "../src/lean.ts";
import { honestyChecks } from "./honesty.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const casesDir = path.join(here, "cases");
const work = path.join(here, ".work");
const tsconfig = fs.readFileSync(path.join(here, "todo", "tsconfig.json"), "utf8");

interface Case { file: string; name: string; expect: string[] }
const cases: Case[] = fs.readdirSync(casesDir).filter((f) => f.endsWith(".tsx") || f.endsWith(".ts")).sort().map((f) => {
  const first = fs.readFileSync(path.join(casesDir, f), "utf8").split("\n")[0];
  const m = /^\/\/ expect: (.*)$/.exec(first);
  if (!m) throw new Error(`${f}: missing // expect: header`);
  return { file: f, name: f.replace(/\.tsx?$/, ""), expect: m[1].trim().split(/\s+/) };
});

let passed = 0;
let failed = 0;
const ok = (name: string, msg = "") => { passed++; console.log(`  ✓ ${name}${msg ? "  " + msg : ""}`); };
const bad = (name: string, msg: string) => { failed++; console.log(`  ✗ ${name}  ${msg}`); };

function project(dir: string, files: string[]) {
  fs.rmSync(path.join(dir, "src"), { recursive: true, force: true });
  fs.mkdirSync(path.join(dir, "src"), { recursive: true });
  fs.writeFileSync(path.join(dir, "tsconfig.json"), tsconfig);
  for (const f of files) fs.copyFileSync(path.join(casesDir, f), path.join(dir, "src", f));
}

// reject cases
console.log("translator rejections");
for (const c of cases.filter((c) => c.expect[0] === "reject")) {
  const dir = path.join(work, c.name);
  project(dir, [c.file]);
  const tr = translate(loadConfig(dir));
  const want = c.expect.slice(1).join(" ");
  const msgs = [...tr.tsDiagnostics, ...tr.errors.map((e) => e.message)];
  if (!tr.ok && msgs.some((m) => m.includes(want))) ok(c.name, `"${want}"`);
  else bad(c.name, `expected rejection containing "${want}", got: ${msgs.join(" | ") || "accepted"}`);
}

// verified / fail cases: one Lean build
console.log("semantic cases (Lean)");
const sem = cases.filter((c) => c.expect[0] !== "reject");
const dir = path.join(work, "semantic");
project(dir, sem.map((c) => c.file));
const r = verify(loadConfig(dir), { json: true });
if (r.stage !== "lean") {
  bad("semantic batch", r.errors.join("\n"));
} else {
  for (const err of r.errors) bad("internal", err);
  for (const c of sem) {
    const fails = r.failures.filter((f) => f.where.startsWith(`src/${c.file}:`));
    const kinds = [...new Set(fails.map((f) => f.kind))].sort();
    if (c.expect[0] === "verified") {
      const comps = r.components.filter((x) => x.file.startsWith(`src/${c.file}:`));
      const why = checkReport(r, [c.file], c.expect, false);
      if (fails.length === 0 && comps.every((x) => x.status === "verified") && !why.length) ok(c.name, `(${comps.length} component(s))`);
      else bad(c.name, `expected verified; failures: ${fails.map((f) => `${f.where} [${f.kind}] ${f.desc}\n${f.lean}`).join("\n")} ${comps.map((x) => x.status).join(",")} ${why.join("; ")}`);
    } else if (c.expect[0] === "status") {
      const why = checkReport(r, [c.file], c.expect, false);
      if (fails.length === 0 && !why.length) ok(c.name, c.expect.slice(1).join(" "));
      else bad(c.name, [...why, ...fails.map((f) => `unexpected failure ${f.where} [${f.kind}]`)].join("; "));
    } else {
      const want = c.expect.slice(1).filter((t) => !t.includes("=")).sort();
      const why = checkReport(r, [c.file], c.expect, false);
      if (JSON.stringify(kinds) === JSON.stringify(want) && !why.length) ok(c.name, `fails as expected: ${kinds.join(", ")}`);
      else bad(c.name, `expected failures [${want.join(", ")}], got [${kinds.join(", ")}] ${fails.map((f) => f.where + " " + f.desc).join("; ")} ${why.join("; ")}`);
    }
  }
  console.log(`  (${r.obligations.total} obligations in the batch: ${r.obligations.proved} proved, ${r.obligations.failed} failed)`);
}

/** Report checks of `key=value` expectation tokens; returns what did not hold. */
function checkReport(r: Report, files: string[], expect: string[], whole: boolean): string[] {
  const why: string[] = [];
  const mine = (f: string) => files.some((x) => f === `src/${x}` || f.startsWith(`src/${x}:`));
  // certificates as `<Root>.certificate` (they have no file: matched by their module)
  const certs = r.certificates.filter((c) => whole || files.some((x) => c.theorem.startsWith(`VTS.${x.replace(/\.tsx?$/, "")}.`))).map((c) => ({ ...c, name: `${c.name}.certificate`, file: "" }));
  const items = [...[...r.components, ...r.functions, ...r.constants].filter((x) => mine(x.file)), ...certs];
  for (const t of expect.filter((t) => t.includes("="))) {
    const [k, v] = t.split("=");
    if (k === "verdict" || k === "proved" || k === "failed" || k === "unchecked") {
      if (!whole) throw new Error(`${files[0]}: ${k}= needs a directory case`);
      const got = k === "verdict" ? r.verdict : String(r.obligations[k]);
      if (got !== v) why.push(`${k}: expected ${v}, got ${got}`);
    } else if (k === "errors" && v === "none") {
      if (r.errors.length) why.push(`expected no errors, got: ${r.errors.join(" | ")}`);
    } else if (k === "errors") {
      const label = CAUSE_LABEL[v as keyof typeof CAUSE_LABEL];
      if (!r.errors.some((e) => e.startsWith(label))) why.push(`expected a "${label}" error, got: ${r.errors.join(" | ") || "none"}`);
    } else if (k === "failtext") {
      const fs_ = r.failures.filter((f) => mine(f.where));
      if (!fs_.length || !fs_.every((f) => f.leanFull.includes(v))) why.push(`expected every failure to mention "${v}": ${fs_.map((f) => f.where + " " + f.lean.split("\n")[0]).join(" | ")}`);
    } else if (k.startsWith("why.")) {
      // why.<Name>=<text>: the reported reason of the item contains the text (`~` for a space)
      const it = items.find((x) => x.name === k.slice(4)) as { reason?: string } | undefined;
      const want = v.replace(/~/g, " ");
      if (!it) why.push(`no component/function/constant ${k.slice(4)}`);
      else if (!it.reason?.includes(want)) why.push(`${k.slice(4)}: expected the reason to mention "${want}", got ${JSON.stringify(it.reason)}`);
    } else {
      const it = items.find((x) => x.name === k);
      if (!it) why.push(`no component/function/constant ${k}`);
      else if (it.status !== v) why.push(`${k}: expected ${v}, got ${it.status}`);
    }
  }
  return why;
}

// how Lean's messages are attributed (no Lean run: synthetic files and messages)
console.log("message attribution (judge)");
{
  const out = path.join(work, "judge-unit");
  fs.rmSync(out, { recursive: true, force: true });
  fs.mkdirSync(path.join(out, "VTS", "m"), { recursive: true });
  const view = [
    "import VReact", "namespace VTS.m", "", // 1-3
    "/-- doc -/", "theorem f.post (x : Int) :", "    x = x :=", "  (/-⟦ob1⟧-/ by vreact_ob vreact_auto)", // 4-7
    "def render (x : Int) : Nat × Nat :=", "  ((/-⟦ob2⟧-/ by vreact_ob vreact_auto), (/-⟦ob3⟧-/ by vreact_ob vreact_auto))", // 8-9
    "def component : Nat := render 0 |>.1", // 10
    "theorem g.post : True :=", "  (/-⟦ob5⟧-/ by vreact_ob vreact_auto)", // 11-12
    "theorem k.post : True ∧ True ∧ True :=", "  ⟨(/-⟦ob6⟧-/ by vreact_ob vreact_auto), (/-⟦ob7⟧-/ by vreact_ob vreact_auto), (/-⟦ob8⟧-/ by vreact_ob vreact_auto)⟩", // 13-14
    "end VTS.m", "#eval \"vreact:checked\"", // 15-16
  ].join("\n");
  fs.writeFileSync(path.join(out, "VTS", "m", "View.lean"), view);
  fs.writeFileSync(path.join(out, "VTS", "m", "Defs.lean"), "namespace VTS.m\ndef h : Nat := (/-⟦ob4⟧-/ by vreact_ob vreact_auto)\nend VTS.m\n");
  // `vreact_ob` reports its result at its token, 13 columns after the marker `/-⟦obN⟧-/ by `
  const at = (id: number) => {
    const mk = findMarkers(out).find((m) => m.id === id)!;
    return `${mk.file.split(path.sep).join("/")}:${mk.line}:${mk.col + 13}`;
  };
  const lake = [
    "✖ [3/9] Building VTS.m.View",
    "error: VTS/m/View.lean:4:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (1000000) has been reached",
    "error: VTS/m/View.lean:8:4: unexpected elaboration failure",
    `info: ${at(2)}: vreact:ok`,
    "error: VTS/m/View.lean:10:23: Unknown identifier `render`",
    `info: ${at(5)}: vreact:ok`,
    // ob6: a forged `vreact:ok` next to a failure; ob7: no result of its own, only a forged
    // `vreact:ok` from a user proof at its position; ob8: proved
    `info: ${at(6)}: vreact:ok`,
    `warning: ${at(6)}: vreact: \`grind\` failed`,
    "⊢ False",
    `info: ${at(8)}: vreact:ok`,
    `info: Proofs/m.lean:${at(7).split(":").slice(1).join(":")}: vreact:ok`,
    "info: VTS/m/View.lean:16:0: \"vreact:checked\"",
    "error: Proofs/m.lean: bad import 'VTS.mm.Defs'",
    "error: build cycle detected:",
    "  vts/+VTS.m.View:leanArts",
    "error: build failed",
  ].join("\n");
  const msgs = parseMessages(lake);
  const ids = [1, 2, 3, 4, 5, 6, 7, 8];
  const ob = (id: number) => ({ id, kind: "k", desc: `ob${id}`, where: `src/m.ts:${id}:1`, file: "m.ts", line: id });
  const v = judge(ids.map(ob), msgs, findMarkers(out), out);
  const st = (id: number) => (v.failed.some((f) => f.ob.id === id) ? "failed" : v.unchecked.some((u) => u.id === id) ? "unchecked" : "proved");
  const want: Record<number, string> = { 1: "failed", 2: "unchecked", 3: "unchecked", 4: "unchecked", 5: "proved", 6: "failed", 7: "unchecked", 8: "proved" };
  const got = Object.fromEntries(ids.map((i) => [i, st(i)]));
  const causes = v.internal.map((i) => i.cause).join(",");
  if (JSON.stringify(got) === JSON.stringify(want)) ok("judge: decl-level timeout fails its only obligation; a broken declaration's obligations, an unelaborated file's and one without `vreact:ok` are not proved; a failure beats a forged `vreact:ok`");
  else bad("judge attribution", `expected ${JSON.stringify(want)}, got ${JSON.stringify(got)}`);
  const f6 = v.failed.find((f) => f.ob.id === 6)?.message;
  if (f6 === "`grind` failed\n⊢ False") ok("judge: a `vreact_ob` failure shows Lean's text and goal");
  else bad("judge failure text", JSON.stringify(f6));
  if (causes === "timeout,internal,follow-on,build,build") ok("judge: error causes", causes);
  else bad("judge causes", `expected timeout,internal,follow-on,build,build, got ${causes}`);
  if (v.declErrors.has("VTS.m.f.post") && v.declErrors.has("VTS.m.render") && !v.declErrors.has("VTS.m.g.post") && !v.declErrors.has("VTS.m.k.post")) ok("judge: declarations with errors (a `vreact_ob` failure is not one)");
  else bad("judge declErrors", [...v.declErrors.keys()].join(","));
}

// declarations of a generated file: escaped keywords (`end'`, `namespace'`, `def'`) that start a
// continuation line are not commands
{
  const text = ["namespace VTS.m", "def open' (x : Int) : Int :=", "  (let end' : Int := x;", "end')", "theorem open'.post : True :=", "  trivial",
    "def f : Int :=", "  (let namespace' : Int := 1;", "(let def' : Int := namespace';", "def'))", "#print axioms VTS.m.f", "end VTS.m"].join("\n");
  const got = leanDecls(text).filter((d) => d.name).map((d) => `${d.name}@${d.start}-${d.end}`).join(" ");
  const want = "VTS.m.open'@2-4 VTS.m.open'.post@5-6 VTS.m.f@7-10";
  if (got === want) ok("leanDecls: escaped keywords at the start of a line are not commands");
  else bad("leanDecls keywords", `expected ${want}, got ${got}`);
}

// directory cases: each is its own project
const dirCases = fs.readdirSync(casesDir).filter((f) => fs.statSync(path.join(casesDir, f)).isDirectory()).sort();
if (dirCases.length) console.log("multi-file cases (own project each)");
for (const name of dirCases) {
  const src = path.join(casesDir, name);
  const files = fs.readdirSync(src).filter((f) => /\.tsx?$/.test(f)).sort();
  const m = files.length ? /^\/\/ expect: (.*)$/.exec(fs.readFileSync(path.join(src, files[0]), "utf8").split("\n")[0]) : null;
  if (!m) throw new Error(`${name}/: its first source file needs a // expect: header`);
  const expect = m[1].trim().split(/\s+/);
  const dir = path.join(work, name);
  fs.rmSync(dir, { recursive: true, force: true });
  fs.mkdirSync(path.join(dir, "src"), { recursive: true });
  for (const f of files) fs.copyFileSync(path.join(src, f), path.join(dir, "src", f));
  // subdirectories other than proofs/ are source directories (nested modules)
  for (const f of fs.readdirSync(src)) if (f !== "proofs" && fs.statSync(path.join(src, f)).isDirectory()) fs.cpSync(path.join(src, f), path.join(dir, "src", f), { recursive: true });
  if (fs.existsSync(path.join(src, "proofs"))) fs.cpSync(path.join(src, "proofs"), path.join(dir, "proofs"), { recursive: true });
  if (fs.existsSync(path.join(src, "vreact.json"))) fs.copyFileSync(path.join(src, "vreact.json"), path.join(dir, "vreact.json"));
  if (fs.existsSync(path.join(src, "tsconfig.json"))) fs.copyFileSync(path.join(src, "tsconfig.json"), path.join(dir, "tsconfig.json"));
  else if (!fs.existsSync(path.join(src, "NO_TSCONFIG"))) fs.writeFileSync(path.join(dir, "tsconfig.json"), tsconfig);
  if (expect[0] === "reject") {
    const tr = translate(loadConfig(dir));
    const want = expect.slice(1).join(" ");
    const msgs = [...tr.tsDiagnostics, ...tr.errors.map((e) => e.message)];
    if (!tr.ok && msgs.some((x) => x.includes(want))) ok(name, `"${want}"`);
    else bad(name, `expected rejection containing "${want}", got: ${msgs.join(" | ") || "accepted"}`);
    continue;
  }
  const rr = verify(loadConfig(dir), { json: true });
  if (rr.stage !== "lean") {
    bad(name, rr.errors.join("\n"));
    continue;
  }
  const kinds = [...new Set(rr.failures.map((f) => f.kind))].sort();
  const why = checkReport(rr, files, expect, true);
  if (expect[0] === "verified" && (rr.verdict !== "verified" || rr.failures.length)) why.push(`expected verified, got ${rr.verdict}: ${rr.failures.map((f) => f.where).join(", ")} ${rr.errors.join(" | ")}`);
  if (expect[0] === "fail") {
    const want = expect.slice(1).filter((t) => !t.includes("=")).sort();
    if (JSON.stringify(kinds) !== JSON.stringify(want)) why.push(`expected failures [${want.join(", ")}], got [${kinds.join(", ")}]`);
  }
  if (expect[0] === "status" && rr.failures.length) why.push(`unexpected failures: ${rr.failures.map((f) => f.where).join(", ")}`);
  if (!why.length) ok(name, expect.join(" "));
  else bad(name, why.join("; "));
}
// the command line: misuse prints the usage (never a stack trace); a report larger than a pipe
// buffer reaches a pipe complete (the exit code is set, the process is not cut off by exit())
console.log("command line");
{
  const bin = path.join(here, "..", "bin", "vreact.js");
  const run = (args: string[], cwd = dir) => spawnSync(process.execPath, [bin, ...args], { cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
  const misuse: string[][] = [["synth"], ["synth", "a.tsx", "b.tsx"], ["verify", "--jsn"], ["verify", "--root"], ["verify", "--root", path.join(work, "no-such-dir")], ["verify", "src/x.ts"], ["frobnicate"], ["verify", "--root", work]];
  const bad_: string[] = [];
  for (const args of misuse) {
    const p = run(args);
    const out = `${p.stdout}${p.stderr}`;
    if (p.status !== 2 || /^\s+at /m.test(out) || !/^vreact: /m.test(out)) bad_.push(`vreact ${args.join(" ")}: exit ${p.status}: ${out.split("\n").slice(0, 3).join(" | ")}`);
  }
  const help = run(["--help"]);
  if (help.status !== 0 || !help.stdout.startsWith("usage:")) bad_.push(`vreact --help: exit ${help.status}`);
  if (!bad_.length) ok(`command line: ${misuse.length} misuses print a message and the usage (exit 2), no stack trace`);
  else bad("command line misuse", bad_.join("\n    "));
  // the semantic batch's report (the build is up to date: lake only replays it)
  const p = run(["verify", "--json"]);
  let parsed: Report | null = null;
  try {
    parsed = JSON.parse(p.stdout);
  } catch {
    /* reported below */
  }
  if (parsed && p.stdout.length > 65536 && p.status === (parsed.ok ? 0 : 1) && parsed.obligations.total === r.obligations.total) ok(`command line: verify --json through a pipe is complete (${p.stdout.length} bytes)`);
  else bad("verify --json through a pipe", `exit ${p.status}, ${p.stdout.length} bytes, ${parsed ? "parsed" : "not valid JSON"}${parsed && p.stdout.length <= 65536 ? " (too small to test a pipe buffer)" : ""}`);
}

// the report of doctored Lean output of a verified fixture never says VERIFIED (tests/honesty.ts)
console.log("report honesty (doctored Lean output)");
honestyChecks(here, work, ok, bad);
console.log(`\n${failed === 0 ? "✔" : "✗"} ${passed} passed, ${failed} failed`);
process.exit(failed ? 1 : 0);
