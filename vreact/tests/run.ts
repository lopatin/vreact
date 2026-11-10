/**
 * Regression suite: every case file starts with
 *   // expect: verified | fail <kind…> | reject <message substring> | status
 * `verified`/`fail`/`status` cases are checked together in one Lean build; `reject` cases
 * must be refused by the translator with the given message. Tokens `key=value` add
 * report checks (see `checkReport`): `Name=<status>` for a component/function/constant of
 * the case, `verdict=…`, `proved=N`, `unchecked=N`, `errors=<cause>`, `failtext=<text>`
 * (every failure's Lean text contains it; `~` stands for a space),
 * `faildesc=<text>` (every failure's description; `~` stands for a space), `uncheckedwhy=<text>`
 * (every not-checked obligation's reason; `~` stands for a space),
 * `why.Name=<text>` (the item's reported reason mentions the text; `~` stands for a space).
 * A directory `cases/<Name>/` is a multi-file case with its own project: its .ts/.tsx files
 * and subdirectories go to src/, `proofs/` and `vreact.json` are copied, `_node_modules/` becomes
 * the project's `node_modules/` (installed libraries), `tsconfig.json` replaces the default
 * one (a file `NO_TSCONFIG` means none); the header of its first source file applies. Files in
 * `smuggled/` replace the proof files of the same name in the generated project after the
 * translation (a proof the whitelist would reject: the report must stay honest regardless).
 * A case whose header is `// expect: synth …` runs `vreact synth` on its (first) source file, in
 * its own project, instead of verifying it (see `synthCase` for its tokens).
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import ts from "typescript";
import { loadConfig, verify, reportFrom, CAUSE_LABEL, type Report } from "../src/cli.ts";
import { translate, moduleNs } from "../src/module.ts";
import { parseMessages, judge, findMarkers, leanDecls, leanBin, runLake, summarizeLeanError } from "../src/lean.ts";
import { editorProject, LAKEFILE_MARKER } from "../src/ide.ts";
import { argText, nodeText, exprText } from "../src/util.ts";
import { synthCommand, type SynthResult } from "../src/synth.ts";
import { honestyChecks } from "./honesty.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const casesDir = path.join(here, "cases");
const work = path.join(here, ".work");
const tsconfig = fs.readFileSync(path.join(here, "todo", "tsconfig.json"), "utf8");

// `node tests/run.ts Gx Mx`: only the cases (files and directories) whose names start with one
// of the given prefixes; the command-line, Lean editor file and honesty checks run only on a full run
const only = process.argv.slice(2);
const selected = (name: string) => only.length === 0 || only.some((p) => name.startsWith(p));

interface Case { file: string; name: string; expect: string[] }
const cases: Case[] = fs.readdirSync(casesDir).filter((f) => (f.endsWith(".tsx") || f.endsWith(".ts")) && selected(f)).sort().map((f) => {
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
  // (a problem is reported once, also when the translation reaches it twice: MxRejectOptValueOnce)
  const at = tr.errors.map((e) => `${e.line}:${e.col}: ${e.message}`);
  const dup = at.find((x, i) => at.indexOf(x) !== i);
  if (dup) bad(c.name, `error reported twice: ${dup}`);
  else if (!tr.ok && msgs.some((m) => m.includes(want))) ok(c.name, `"${want}"`);
  else bad(c.name, `expected rejection containing "${want}", got: ${msgs.join(" | ") || "accepted"}`);
}

// verified / fail cases: one Lean build
console.log("semantic cases (Lean)");
const sem = cases.filter((c) => c.expect[0] !== "reject" && c.expect[0] !== "synth");
const dir = path.join(work, "semantic");
project(dir, sem.map((c) => c.file));
const r = sem.length || !only.length ? verify(loadConfig(dir), { json: true }) : null;
if (r === null) {
  console.log("  (no semantic case selected)");
} else if (r.stage !== "lean") {
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

/**
 * Doctor the build logs lake stored with the generated modules (`<out>/.lake/build/…/VTS/**.trace`,
 * which lake replays as Lean's output when a module is up to date) so that they claim success:
 * `vreact:` failures become `vreact:ok`, `sorry` warnings go, axiom reports with `sorryAx` become
 * clean (round-2 finding r4-lean-r2-cache-poison). Returns the number of entries changed.
 */
function poisonTraces(outDir: string): number {
  let n = 0;
  const walk = (d: string) => {
    if (!fs.existsSync(d)) return;
    for (const f of fs.readdirSync(d)) {
      const p = path.join(d, f);
      if (fs.statSync(p).isDirectory()) walk(p);
      else if (f.endsWith(".trace")) {
        const t = JSON.parse(fs.readFileSync(p, "utf8")) as { log?: { level: string; message: string }[] };
        if (!Array.isArray(t.log)) continue;
        t.log = t.log
          .filter((e) => !/declaration uses .sorry./.test(e.message) || (n++, false))
          .map((e) => {
            if (e.level === "warning" && /: vreact: /.test(e.message)) return n++, { level: "info", message: e.message.replace(/: vreact: [\s\S]*$/, ": vreact:ok") };
            if (/depends on axioms: \[[^\]]*sorryAx[^\]]*\]/.test(e.message)) return n++, { ...e, message: e.message.replace(/depends on axioms: \[[^\]]*\]/, "does not depend on any axioms") };
            return e;
          });
        fs.writeFileSync(p, JSON.stringify(t));
      }
    }
  };
  walk(path.join(outDir, ".lake", "build", "lib", "lean", "VTS"));
  return n;
}

/** Report checks of `key=value` expectation tokens; returns what did not hold. */
function checkReport(r: Report, files: string[], expect: string[], whole: boolean): string[] {
  const why: string[] = [];
  const mine = (f: string) => files.some((x) => f === `src/${x}` || f.startsWith(`src/${x}:`));
  // certificates as `<Root>.certificate` (they have no file: matched by their module)
  const certs = r.certificates.filter((c) => whole || files.some((x) => c.theorem.startsWith(`VTS.${x.replace(/\.tsx?$/, "")}.`))).map((c) => ({ ...c, name: `${c.name}.certificate`, file: "" }));
  const items = [...[...r.components, ...r.functions, ...r.constants].filter((x) => mine(x.file)), ...certs];
  for (const t of expect.filter((t) => t.includes("="))) {
    const at = t.indexOf("=");
    const [k, v] = [t.slice(0, at), t.slice(at + 1)];
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
      // failtext=<text>: every failure's Lean text contains the text (`~` for a space)
      const want = v.replace(/~/g, " ");
      const fs_ = r.failures.filter((f) => mine(f.where));
      if (!fs_.length || !fs_.every((f) => f.leanFull.includes(want))) why.push(`expected every failure to mention "${want}": ${fs_.map((f) => f.where + " " + f.lean.split("\n")[0]).join(" | ")}`);
    } else if (k === "uncheckedwhy") {
      // uncheckedwhy=<text>: every obligation of the case that was not checked has a reason that contains the text (`~` for a space)
      const want = v.replace(/~/g, " ");
      const us = r.notChecked.filter((u) => mine(u.where));
      if (!us.length || !us.every((u) => u.reason.includes(want))) why.push(`expected every not-checked obligation's reason to mention "${want}": ${us.map((u) => u.where + " " + u.reason).join(" | ") || "none"}`);
    } else if (k === "faildesc") {
      // faildesc=<text>: every failure's description (what the report prints after [kind]) contains the text (`~` for a space)
      const want = v.replace(/~/g, " ");
      const fs_ = r.failures.filter((f) => mine(f.where));
      if (!fs_.length || !fs_.every((f) => f.desc.includes(want))) why.push(`expected every failure description to mention "${want}": ${fs_.map((f) => f.where + " " + f.desc).join(" | ")}`);
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
    // ob6: a forged `vreact:ok` next to a failure; ob7: no result of its own, only forged
    // `vreact:ok`s from a user proof (at its position in the proof file, and as a line of a
    // message the proof printed: `#print "x\ninfo: <ob7's position>: vreact:ok"`, which lake
    // prints in the proof's job log); ob8: proved
    `info: ${at(6)}: vreact:ok`,
    `warning: ${at(6)}: vreact: \`grind\` failed`,
    "⊢ False",
    `info: ${at(8)}: vreact:ok`,
    "info: VTS/m/View.lean:16:0: \"vreact:checked\"",
    "✔ [4/9] Built Proofs.m",
    `info: Proofs/m.lean:${at(7).split(":").slice(1).join(":")}: vreact:ok`,
    "info: Proofs/m.lean:3:0: x",
    `info: ${at(7)}: vreact:ok`,
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
  // (round-1 finding r4-lean-forge-print) an info naming a generated file counts only in the
  // job log of that file's module: in the proof's log it is a line of the proof's message
  const [f7, l7, c7] = at(7).split(":");
  const forged = msgs.filter((x) => x.file === f7 && x.line === +l7 && x.col === +c7);
  const host = msgs.find((x) => x.file === "Proofs/m.lean" && x.line === 3);
  if (!forged.length && host?.text === `x\ninfo: ${at(7)}: vreact:ok`) ok("parseMessages: a user proof's message line that reads like a generated file's message stays in the proof's message (RlForgedPrint)");
  else bad("parseMessages job logs", `forged: ${JSON.stringify(forged)}, proof message: ${JSON.stringify(host?.text)}`);
  if (v.declErrors.has("VTS.m.f.post") && v.declErrors.has("VTS.m.render") && !v.declErrors.has("VTS.m.g.post") && !v.declErrors.has("VTS.m.k.post")) ok("judge: declarations with errors (a `vreact_ob` failure is not one)");
  else bad("judge declErrors", [...v.declErrors.keys()].join(","));
}

// the short report's goal (summarizeLeanError, 18 lines), on real failure texts of the
// options-chain walkthrough (tests/goals/, cut after grind's first diagnostics lines): what stands
// for other lines names and counts them, every other line is a whole hypothesis of the goal (the
// conclusion may end in `…`), and the hypotheses that decide the case stay in view
{
  const goal = (f: string) => fs.readFileSync(path.join(here, "goals", f), "utf8");
  const blocksOf = (lines: string[]) => {
    const bs: string[][] = [];
    for (const l of lines) {
      if (/^\s/.test(l) && bs.length) bs[bs.length - 1].push(l);
      else bs.push([l]);
    }
    return bs.map((b) => b.join("\n"));
  };
  const standIn = (l: string) => /: --full shows (it|them)\)$/.test(l);
  /** why `out` is not made of stand-ins and whole blocks of `text` ("" if it is) */
  const pieces = (text: string, out: string[]) => {
    const lines = text.split("\n");
    const cut = lines.findIndex((l) => /\[grind\] Goal diagnostics/.test(l));
    const ins = new Set(blocksOf((cut > 0 ? lines.slice(0, cut) : lines).filter((l) => l.trim() !== "")));
    const outs = blocksOf(out.filter((l) => !standIn(l)));
    const cutTarget = (b: string) => b.startsWith("⊢") && b.endsWith("\n  …") && [...ins].some((i) => i.startsWith(b.slice(0, -"\n  …".length) + "\n"));
    const odd = outs.filter((b) => !ins.has(b) && !cutTarget(b));
    return odd.length ? `not a whole hypothesis: ${JSON.stringify(odd[0].slice(0, 80))}` : "";
  };
  const why: string[] = [];
  const check = (f: string, conds: [string, (o: string[]) => boolean][]) => {
    const text = goal(f);
    const out = summarizeLeanError(text, 18).split("\n");
    if (out.length > 18) why.push(`${f}: ${out.length} lines`);
    const p = pieces(text, out);
    if (p) why.push(`${f}: ${p}`);
    for (const [what, c] of conds) if (!c(out)) why.push(`${f}: ${what}`);
  };
  const above = (o: string[], line: string) => o[o.indexOf("⊢ False") - 1] === line;
  // step 20: the deciding `h` stays; the 4-line definition `marketable := match …` is one line
  check("orderticket-price.txt", [
    ["h right above the conclusion", (o) => above(o, "h : σ.price + -1 ≤ 0")],
    ["marketable as one line", (o) => o.includes("marketable := …  (a definition, 4 lines: --full shows it)") && !o.some((l) => l.includes("match h₁ : m with"))],
    ["the short hypotheses before it", (o) => ["hpre : props.ticket.price > 0", "m : Option model.Quote := props.market", "hinv : (1 ≤ σ.qty ∧ σ.qty ≤ 500) ∧ σ.price > 0"].every((l) => o.includes(l))],
  ]);
  // step 40: the 8-line `h_1` next to the conclusion (the total after `set`) stays whole: a
  // 3-line hypothesis above it becomes one line, and two short lines at the top are left out
  check("place-cap.txt", [
    ["h_1 whole", (o) => { const i = o.indexOf("h_1 :"); return i > 0 && o[i + 7] === "    0" && o[i + 8] === "left : JS.eq t.side model.Side.ask = true"; }],
    ["h₂₇ as one line", (o) => o.includes("h₂₇ : …  (a long hypothesis, 3 lines: --full shows it)")],
    ["u and t named as left out", (o) => o[2] === "  … (2 earlier hypotheses: u, t: --full shows them)"],
  ]);
  // step 14: definitions and long hypotheses become one line each; `h` (atmIndex returned -1) and
  // the filter's case stay, the hypotheses farthest from the conclusion are named as left out
  check("atm-edge.txt", [
    ["h and h₂₂ h_7 kept", (o) => o.includes("h : (JS.findIndex e.strikes fun s => model.nearest e.strikes s held_1) + 1 ≤ 0") && o.includes("h₂₂ h_7 : σ.ui.filter = model.StrikeFilter.s3")],
    ["center, atm as one line", (o) => o.includes("center, atm := …  (2 definitions, 8 lines: --full shows them)")],
    ["long hypotheses as one line", (o) => o.some((l) => /^h₁₀, hpre, hinv, heq, h₈, h_5 : …  \(6 long hypotheses, \d+ lines: --full shows them\)$/.test(l))],
    ["the earlier ones named", (o) => /^  … \(\d+ earlier hypotheses: E, props, κ, σ, ui, ticket, levels, allOpen, …: --full shows them\)$/.test(o[2])],
  ]);
  // step 45: a 180-line hypothesis (`left`) and 6 multi-line definitions; what is shown is whole
  check("watch-dup-keys.txt", [
    ["ends with the conclusion", (o) => o[o.length - 1] === "⊢ False"],
    ["definitions as one line", (o) => o.includes("tExp, center, atm, span, rows, liveAtm := …  (6 definitions, 24 lines: --full shows them)")],
    ["left among the long hypotheses", (o) => o.some((l) => /^hpre, hinv, left, .* : …  \(\d+ long hypotheses, \d+ lines: --full shows them\)$/.test(l))],
  ]);
  // step 35: the contract instances (125 lines) become one line; the rest fits
  check("sim-clocks.txt", [
    ["contracts as one line", (o) => o.includes("hcontract, hcontract_1, hcontract_2, hcontract_3 : …  (4 contract instances, 125 lines: --full shows them)")],
    ["the deciding hypotheses", (o) => ["h₁₆ : ¬s.rally = true", "h : ¬s.paused = true", "h_1 : ¬40 ≤ s.feed.offset"].every((l) => o.includes(l))],
  ]);
  // (6491f44) after a timeout with a failing case: the case's own hypotheses above its conclusion,
  // none of the goal as stated (its hypotheses are lines of the text before the case's)
  {
    const text = goal("timeout-failing-case.txt");
    const caseStart = text.indexOf("\n`grind` failed\n");
    const caseLines = new Set(text.slice(caseStart).split("\n"));
    check("timeout-failing-case.txt", [
      ["the stated goal is one line", (o) => o[1] === "  … (the goal as stated: --full shows it)" && !o.some((l) => l.startsWith("⊢ paused = true"))],
      ["the case's name, then its hypotheses", (o) => { const c = o.indexOf("case grind.1.1.1.2"); return c > 0 && o.slice(c, o.indexOf("⊢ False")).every((l) => standIn(l) || caseLines.has(l)); }],
      ["the case's last hypothesis above its conclusion", (o) => above(o, "h_8 : ¬f.seed + -872 ≤ 0")],
    ]);
  }
  // a timeout whose first unfinished case has a long conclusion: cut to 3 lines and `…`
  check("timeout-unfinished-case.txt", [
    ["the case", (o) => o.includes("case h_1.isFalse.isTrue") && o[1] === "  … (the goal as stated: --full shows it)"],
    ["the 3-line hypothesis right above the conclusion whole", (o) => { const i = o.indexOf("hkey✝ :"); return i > 0 && o[i + 3].startsWith("⊢ ∀"); }],
    ["the conclusion cut", (o) => o[o.length - 1] === "  …" && o[o.length - 4].startsWith("⊢ ")],
  ]);
  // a 4-line hypothesis at the top that frees more lines than needed is one line where it was
  // (it was left out, as "an earlier hypothesis")
  const one = ["`grind` failed", "case grind", "h0 :", "  0 ≤ a ∧", "    a < 3 ∧", "    b = 1", ...Array.from({ length: 13 }, (_, i) => `x_${i} : Int`), "⊢ False"].join("\n");
  const oneOut = summarizeLeanError(one, 18).split("\n");
  if (oneOut[2] !== "h0 : …  (a long hypothesis, 4 lines: --full shows it)" || oneOut.length !== 17 || oneOut.some((l) => l.startsWith("  … ("))) why.push(`one at the top: ${oneOut.slice(0, 4).join(" / ")}`);
  // the hypothesis right above the conclusion (here the negated goal, 4 lines) stays whole when it
  // fits: the short hypotheses farthest from the conclusion are left out instead (it was one line
  // "h : …", with 13 short hypotheses above it)
  const neg = ["`grind` failed", "case grind", ...Array.from({ length: 20 }, (_, i) => `x_${i} : Int`), "h :", "  ¬(0 ≤ a ∧", "      a < 3 ∧", "      b = 1)", "⊢ False"].join("\n");
  const negOut = summarizeLeanError(neg, 18).split("\n");
  if (negOut.length > 18 || negOut[2] !== "  … (10 earlier hypotheses: x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, …: --full shows them)" || negOut.slice(-5).join("\n") !== "h :\n  ¬(0 ≤ a ∧\n      a < 3 ∧\n      b = 1)\n⊢ False")
    why.push(`the negated goal above the conclusion: ${negOut.slice(-6).join(" / ")}`);
  // a hypothesis too long to fit, next to the conclusion or between short ones, is one line
  // where it was, and the short hypotheses around it stay (the report was the conclusion alone,
  // or the short ones above it were left out: the walk from the conclusion stopped at it)
  const big = (name: string) => [`${name} :`, ...Array.from({ length: 19 }, (_, i) => `  t_${i} ∧`)];
  const shortHs = ["h_a : x = 1", "h_b : ¬y = 2", "h_c : z ≤ 0", "h_d : w = 3", "h_e : ¬v = 0"];
  for (const [what, hs, want] of [
    ["last", [...shortHs, ...big("h_neg")], [...shortHs, "h_neg : …  (a long hypothesis, 20 lines: --full shows it)"]],
    ["in the middle", [...shortHs.slice(0, 2), ...big("hinv"), ...shortHs.slice(2)], [...shortHs.slice(0, 2), "hinv : …  (a long hypothesis, 20 lines: --full shows it)", ...shortHs.slice(2)]],
  ] as [string, string[], string[]][]) {
    const got = summarizeLeanError(["`grind` failed", "case grind", ...hs, "⊢ False"].join("\n"), 18);
    const exp = ["`grind` failed", "case grind", ...want, "⊢ False"].join("\n");
    if (got !== exp) why.push(`a 20-line hypothesis ${what}: ${JSON.stringify(got)}`);
  }
  const short = "`grind` failed\ncase grind.1\ns : Sim\nhcontract :\n  0 ≤ s.feed.seed →\n  0 ≤ 1\n⊢ False";
  if (summarizeLeanError(short, 18) !== short) why.push("a goal that fits was changed");
  if (!why.length) ok("summarizeLeanError: contract instances, long definitions and long hypotheses become one line each, the hypotheses next to the conclusion stay whole, the left-out ones are named; after a timeout only the case's goal; a goal that fits is unchanged");
  else bad("summarizeLeanError", why.join("; "));
}

// the source text in descriptions: literal contents exact (whitespace collapsed only outside
// string, template and regular expression literals); a contract whole up to 120 characters, a
// longer one by the parts of its outer call or operator, each with its start and its end
{
  const src = 'f(\n  { kind: "place",\n    note: "a   b" },\n  `x   y\n  ${a   +  b}  z`,\n  /a  b/.test(s),\n' +
    '  forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, levels)) && r.size === ks.length && sameView(u, r),\n' +
    '  implies(u.orders.has(id) && price > 0 && somethingElseThatIsLong(u, id, price), repriced(u.orders.get(id), r.orders.get(id), price, extraArgument)),\n' +
    '  sameView(u, { ...r, collapsed: u.collapsed, focus: u.focus, watch: u.watch, held: u.held }) && sameMembersExcept(u.collapsed, r.collapsed, id) && r.nextId === u.nextId\n);';
  const sf = ts.createSourceFile("t.ts", src, ts.ScriptTarget.Latest, true);
  const [obj, tpl, re, chain, imp, conj] = ((sf.statements[0] as ts.ExpressionStatement).expression as ts.CallExpression).arguments;
  const why: string[] = [];
  const want = (what: string, got: string, exp: string) => { if (got !== exp) why.push(`${what}: ${JSON.stringify(got)}`); };
  want("nodeText of an object", nodeText(obj), '{ kind: "place", note: "a   b" }');
  want("argText of an object", argText(obj, 20), '{ kind: "place", note: "a   b" }');
  want("a template literal", nodeText(tpl), "`x   y\\n  ${a + b}  z`");
  want("a regular expression", nodeText(re), "/a  b/.test(s)");
  want("a contract that fits", exprText(chain), "forall(0, n, (i) => (r.lo <= i && i < r.hi) === inWindow(i, atm, levels)) && r.size === ks.length && sameView(u, r)");
  for (const [what, e, end] of [["implies", imp, ", price, extraArgument))"], ["a conjunction", conj, " && r.nextId === u.nextId"]] as [string, ts.Node, string][]) {
    const t = exprText(e);
    if (t.length > 120 || !t.endsWith(end) || !t.includes("…")) why.push(`${what} of ${nodeText(e, 400).length} characters: ${JSON.stringify(t)}`);
  }
  if (!exprText(imp).startsWith("implies(u.orders.has(id) && price")) why.push(`implies: the start: ${JSON.stringify(exprText(imp))}`);
  // inside literals, escapes as written and line terminators as escapes (`a\\` + line break was
  // shown `a\b`, another escape; a lone CR or a U+2028 was printed as it is, breaking the line);
  // a long call by its parts keeps its type arguments (`same<int>(…)` was shown `same(…)`)
  const src2 = "f(`a\\\\\nb`, `c\rd`, 'e\u2028f', same<int>(r.filter((x) => x > 0 && x < 1000000 && x !== 7), xs.filter((x) => x > 0 && x < 1000000 && x !== 7 && x !== 3)));";
  const [esc, cr, ls, targs] = (((ts.createSourceFile("u.ts", src2, ts.ScriptTarget.Latest, true).statements[0] as ts.ExpressionStatement).expression) as ts.CallExpression).arguments;
  want("an escaped backslash before a line break", nodeText(esc), "`a\\\\\\nb`");
  want("a lone CR in a template", nodeText(cr), "`c\\nd`");
  want("a U+2028 in a string", nodeText(ls), "'e\\u2028f'");
  if (!exprText(targs).startsWith("same<int>(r.filter(") || exprText(targs).length > 120) why.push(`type arguments: ${JSON.stringify(exprText(targs))}`);
  if (!why.length) ok("descriptions: literal contents exact; a contract whole up to 120 characters, a longer one by its parts, each with its start and end");
  else bad("descriptions", why.join("; "));
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

/**
 * `// expect: synth <token…>`: `vreact synth` on the case's source file `file` (in project `dir`).
 * Tokens: `write` (--write), `size=N` (the largest candidate size), `seconds=N` (the search time
 * of one hole), `<Fn>=<fill>` (the proved fill of the first hole of function Fn; `<Fn>#k=<fill>`
 * of its k-th; `-`: none proved), `<Fn>.status=<status>` (of each hole of Fn), `out=<text>` /
 * `noout=<text>` (synth's output contains / does not contain the text), `written=<text>` /
 * `absent=<text>` (the file's code, without its `//` comments, contains / does not contain it after
 * the run), `unchanged` (the file is as before), `maxsecs=N` (the run took less than N seconds).
 * `~` stands for a space.
 */
async function synthCase(name: string, dir: string, file: string, expect: string[]) {
  const num = (k: string) => {
    const t = expect.find((x) => x.startsWith(`${k}=`));
    return t === undefined ? undefined : Number(t.slice(k.length + 1));
  };
  const seconds = num("seconds");
  const opts = { write: expect.includes("write"), maxSize: num("size"), timeLimitMs: seconds === undefined ? undefined : seconds * 1000 };
  const src = path.join(dir, "src", file);
  const before = fs.readFileSync(src, "utf8");
  const lines: string[] = [];
  const log = console.log;
  console.log = (...a: unknown[]) => void lines.push(a.join(" "));
  let res: SynthResult[] = [];
  const t0 = Date.now();
  const exitCode = process.exitCode;
  try {
    res = await synthCommand(dir, [path.join("src", file)], opts);
  } catch (e) {
    lines.push(`synth threw: ${(e as Error).stack}`);
  } finally {
    console.log = log;
    process.exitCode = exitCode;
  }
  const secs = (Date.now() - t0) / 1000;
  const out = lines.join("\n");
  const after = fs.readFileSync(src, "utf8");
  const afterCode = after.replace(/\/\/.*$/gm, "");
  const why: string[] = [];
  if (out.includes("synth threw: ")) why.push(out.slice(out.indexOf("synth threw: ")));
  for (const t of expect.slice(1)) {
    const at = t.indexOf("=");
    if (at < 0) {
      if (t === "unchanged" && after !== before) why.push("the file was written");
      else if (t !== "write" && t !== "unchanged") why.push(`unknown synth token ${t}`);
      continue;
    }
    const [k, v0] = [t.slice(0, at), t.slice(at + 1)];
    const v = v0.replace(/~/g, " ");
    if (["size", "seconds"].includes(k)) continue;
    if (k === "out" && !out.includes(v)) why.push(`expected the output to mention "${v}"`);
    else if (k === "noout" && out.includes(v)) why.push(`expected the output not to mention "${v}"`);
    else if (k === "written" && !afterCode.includes(v)) why.push(`expected the file to contain "${v}" after the run, got:\n${after}`);
    else if (k === "absent" && afterCode.includes(v)) why.push(`expected the file not to contain "${v}" after the run, got:\n${after}`);
    else if (k === "maxsecs" && !(secs < Number(v))) why.push(`expected the run to take less than ${v}s, it took ${secs.toFixed(0)}s`);
    else if (k.endsWith(".status")) {
      const rs = res.filter((r) => r.fn === k.slice(0, -7));
      if (!rs.length || !rs.every((r) => r.status === v)) why.push(`${k}: expected ${v}, got ${rs.map((r) => r.status).join(", ") || "no result"}`);
    } else if (!["out", "noout", "written", "absent", "maxsecs"].includes(k)) {
      const m = /^(.*?)(?:#(\d+))?$/.exec(k)!;
      const r = res.filter((x) => x.fn === m[1])[m[2] ? Number(m[2]) - 1 : 0];
      const got = r?.proved ? r.solution : "-";
      if (!r) why.push(`no result for ${k}`);
      else if (got !== v) why.push(`${k}: expected ${v === "-" ? "no proved fill" : v}, got ${got === "-" ? `none (${r.status}: ${r.note ?? ""})` : got}`);
    }
  }
  if (!why.length) ok(name, `synth: ${expect.slice(1).join(" ")}  (${secs.toFixed(0)}s)`);
  else bad(name, `${why.join("; ")}\n--- synth output:\n${out}`);
}

// synth cases given as single files: each in its own project
const synthFiles = cases.filter((c) => c.expect[0] === "synth");
if (synthFiles.length) console.log("synthesis cases");
for (const c of synthFiles) {
  const d = path.join(work, c.name);
  fs.rmSync(d, { recursive: true, force: true });
  project(d, [c.file]);
  await synthCase(c.name, d, c.file, c.expect);
}

// directory cases: each is its own project
const dirCases = fs.readdirSync(casesDir).filter((f) => fs.statSync(path.join(casesDir, f)).isDirectory() && selected(f)).sort();
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
  // subdirectories other than proofs/, smuggled/ and _node_modules/ are source directories (nested
  // modules); _node_modules/ is the project's node_modules/ (installed libraries, e.g. type declarations)
  for (const f of fs.readdirSync(src)) if (f !== "proofs" && f !== "smuggled" && f !== "_node_modules" && fs.statSync(path.join(src, f)).isDirectory()) fs.cpSync(path.join(src, f), path.join(dir, "src", f), { recursive: true });
  if (fs.existsSync(path.join(src, "_node_modules"))) fs.cpSync(path.join(src, "_node_modules"), path.join(dir, "node_modules"), { recursive: true });
  if (fs.existsSync(path.join(src, "proofs"))) fs.cpSync(path.join(src, "proofs"), path.join(dir, "proofs"), { recursive: true });
  if (fs.existsSync(path.join(src, "vreact.json"))) fs.copyFileSync(path.join(src, "vreact.json"), path.join(dir, "vreact.json"));
  if (fs.existsSync(path.join(src, "tsconfig.json"))) fs.copyFileSync(path.join(src, "tsconfig.json"), path.join(dir, "tsconfig.json"));
  else if (!fs.existsSync(path.join(src, "NO_TSCONFIG"))) fs.writeFileSync(path.join(dir, "tsconfig.json"), tsconfig);
  if (expect[0] === "synth") {
    await synthCase(name, dir, files[0], expect);
    continue;
  }
  if (expect[0] === "reject") {
    // several expected messages are separated by ` ;; `; a message is also matched with its
    // location (`proofs/m.lean:4:1: …`, relative to the case's project)
    const tr = translate(loadConfig(dir));
    const wants = expect.slice(1).join(" ").split(" ;; ");
    const msgs = [...tr.tsDiagnostics, ...tr.errors.map((e) => `${e.file ? path.relative(dir, e.file).split(path.sep).join("/") : "?"}:${e.line}:${e.col}: ${e.message}`)];
    const missing = wants.filter((w) => !msgs.some((x) => x.includes(w)));
    if (!tr.ok && !missing.length) ok(name, wants.length > 1 ? `${wants.length} rejections` : `"${wants[0]}"`);
    else bad(name, `expected rejection containing "${missing.join('" and "')}", got: ${msgs.join(" | ") || "accepted"}`);
    continue;
  }
  // `smuggled/<P>.lean` replaces the (whitelisted) `proofs/<P>.lean` in the generated project
  // after the translation: the report must stay honest also about a proof file that got past
  // the whitelist check (defense in depth; the whitelist itself is tested by Rl* cases)
  const smuggled = path.join(src, "smuggled");
  let rr: Report;
  if (fs.existsSync(smuggled)) {
    const cfg = loadConfig(dir);
    const tr = translate(cfg);
    if (!tr.ok) {
      bad(name, `translation failed: ${[...tr.tsDiagnostics, ...tr.errors.map((e) => e.message)].join(" | ")}`);
      continue;
    }
    for (const f of fs.readdirSync(smuggled)) fs.copyFileSync(path.join(smuggled, f), path.join(cfg.outDir, "Proofs", f));
    rr = reportFrom(cfg, tr, runLake(cfg.outDir, cfg.leanLib).messages).report;
  } else rr = verify(loadConfig(dir), { json: true });
  if (rr.stage !== "lean") {
    bad(name, rr.errors.join("\n"));
    continue;
  }
  // a file `POISON` in the case: after the first verify, the build logs lake keeps in the
  // project's `.vreact/.lake` are doctored to claim success, and the project is verified again;
  // both reports must meet the expectations (the second must not take the doctored logs)
  if (fs.existsSync(path.join(src, "POISON"))) {
    const n = poisonTraces(loadConfig(dir).outDir);
    const again = verify(loadConfig(dir), { json: true });
    const why2 = n ? checkReport(again, files, expect, true) : ["nothing to doctor in the build logs"];
    if (why2.length) {
      bad(name, `after doctoring the build logs: ${why2.join("; ")}`);
      continue;
    }
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
if (r && !only.length) {
  const bin = path.join(here, "..", "bin", "vreact.js");
  const run = (args: string[], cwd = dir) => spawnSync(process.execPath, [bin, ...args], { cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
  const misuse: string[][] = [["synth"], ["synth", "a.tsx", "b.tsx"], ["verify", "--jsn"], ["verify", "--root"], ["verify", "--root="], ["verify", "--root", path.join(work, "no-such-dir")], ["verify", "src/x.ts"], ["frobnicate"], ["verify", "--root", work]];
  const bad_: string[] = [];
  for (const args of misuse) {
    const p = run(args);
    const out = `${p.stdout}${p.stderr}`;
    if (p.status !== 2 || /^\s+at /m.test(out) || !/^vreact: /m.test(out)) bad_.push(`vreact ${args.join(" ")}: exit ${p.status}: ${out.split("\n").slice(0, 3).join(" | ")}`);
  }
  // the short report names the kind of each obligation it did not check (ReducerActionPreLong's
  // callback, blocked by the failed precondition)
  const plain = run(["verify"]);
  const lines = plain.stdout.replace(/\x1b\[[0-9;]*m/g, "").split("\n");
  const at = lines.findIndex((l) => /^\d+ obligation\(s\) not checked:$/.test(l));
  const listed = at < 0 ? [] : lines.slice(at + 1).filter((l, i, xs) => xs.slice(0, i + 1).every((x) => x.startsWith("  ")));
  const kinded = /^ {2}src\/\S+:\d+:\d+ \[[a-z-]+\](, src\/\S+:\d+:\d+ \[[a-z-]+\])*(, … \(\d+\))?: /;
  // (a line shows the first four obligations of its reason: when other cases sort before it,
  // ReducerActionPreLong's callback is among the elided ones, `… (n)`, of its reason's line)
  const witness = r.notChecked.find((u) => /^src\/ReducerActionPreLong\.tsx:\d+:\d+$/.test(u.where));
  const witnessLine = !!witness && listed.some((l) => l.includes(`${witness.where} [callback]`) || (/, … \(\d+\): /.test(l) && l.endsWith(`: ${witness.reason}`)));
  if (listed.length && listed.every((l) => kinded.test(l)) && witness?.kind === "callback" && witnessLine) ok(`command line: the "not checked" lines (${listed.length}) name each obligation's kind`);
  else bad("not checked lines", listed.slice(0, 3).join(" | ") || "(none)");
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

// Lean editor support (src/ide.ts): `verify` writes lean-toolchain and vreact's lakefile.toml into
// the app folder, where `lake lean` (what an editor's `lake serve` does per file) resolves
// `import VTS.<module>.Defs` through the generated project; vreact keeps both files in step with the
// library and "out", and never writes them next to a lakefile of the user's (not per-case: only
// on a full run, like the command-line and honesty checks)
console.log("Lean editor files");
if (r && !only.length) {
  const lib = path.join(here, "..", "lean");
  const toolchain = fs.readFileSync(path.join(lib, "lean-toolchain"), "utf8");
  const read = (d: string, f: string) => (fs.existsSync(path.join(d, f)) ? fs.readFileSync(path.join(d, f), "utf8") : null);
  const lakefileOk = (d: string, out: string) => !!read(d, "lakefile.toml")?.startsWith(LAKEFILE_MARKER) && read(d, "lakefile.toml")!.includes(`\npath = ${JSON.stringify(out)}\n`);
  // the semantic batch's folder, written by its `verify` above
  if (read(dir, "lean-toolchain") === toolchain && lakefileOk(dir, ".vreact")) ok("editor files: verify wrote lean-toolchain (the library's) and lakefile.toml (requires .vreact)");
  else bad("editor files after verify", `lean-toolchain ${JSON.stringify(read(dir, "lean-toolchain"))}, lakefile.toml ${JSON.stringify(read(dir, "lakefile.toml"))}`);
  // a proof-like file in the app folder (outside proofs/, which the next run would copy) importing
  // the Defs of a verified case
  const vcase = sem.find((c) => c.expect[0] === "verified" && !r.failures.some((f) => f.where.startsWith(`src/${c.file}:`)));
  if (r.stage === "lean" && vcase) {
    const mod = `${moduleNs(path.join(dir, "src"), path.join(dir, "src", vcase.file))}.Defs`;
    const check = path.join(dir, "EditorCheck.lean");
    fs.writeFileSync(check, `import ${mod}\nexample : (1 : Nat) + 1 = 2 := rfl\n`);
    const bin = leanBin();
    const p = spawnSync("lake", ["lean", "EditorCheck.lean"], { cwd: dir, encoding: "utf8", env: { ...process.env, PATH: bin ? `${bin}:${process.env.PATH}` : process.env.PATH }, maxBuffer: 64 * 1024 * 1024 });
    fs.rmSync(check, { force: true });
    const out = `${p.stdout ?? ""}${p.stderr ?? ""}`;
    if (p.status === 0 && !/^error/m.test(out)) ok(`editor files: lake lean in the app folder resolves import ${mod}`);
    else bad("lake lean in the app folder", `exit ${p.status}${p.error ? ` (${p.error.message})` : ""}: ${out.split("\n").filter((l) => /error/.test(l)).slice(0, 5).join(" | ")}`);
  } else bad("lake lean in the app folder", "no verified case in the semantic batch to import");
  // what is (re)written, without Lean
  const d = path.join(work, "editor-files");
  const reset = () => {
    fs.rmSync(d, { recursive: true, force: true });
    fs.mkdirSync(d, { recursive: true });
  };
  const ed = (out = ".vreact") => editorProject(d, path.join(d, out), path.join(d, "proofs"), lib);
  const why: string[] = [];
  reset();
  fs.writeFileSync(path.join(d, ".gitignore"), "node_modules/\n/.lake");
  const first = ed();
  if (!lakefileOk(d, ".vreact") || read(d, "lean-toolchain") !== toolchain) why.push("a fresh folder did not get both files");
  if (read(d, ".gitignore") !== "node_modules/\n/.lake\nlake-manifest.json\n") why.push(`.gitignore: ${JSON.stringify(read(d, ".gitignore"))}`);
  if (!first.notes.length) why.push("no note for the files written");
  if (ed().notes.length) why.push("a second run rewrote up-to-date files");
  fs.writeFileSync(path.join(d, "lean-toolchain"), "leanprover/lean4:v4.0.0\n");
  fs.writeFileSync(path.join(d, ".gitignore"), "");
  fs.writeFileSync(path.join(d, "lake-manifest.json"), JSON.stringify({ packages: [{ name: "vts", dir: ".vreact" }, { name: "VReact", dir: "/no/such/VReact" }] }));
  ed("gen");
  if (read(d, "lean-toolchain") !== toolchain) why.push("a stale lean-toolchain was not updated");
  if (!lakefileOk(d, "gen")) why.push(`vreact's lakefile.toml does not follow "out": ${JSON.stringify(read(d, "lakefile.toml"))}`);
  if (fs.existsSync(path.join(d, "lake-manifest.json"))) why.push("a manifest naming another VReact was kept");
  if (read(d, ".gitignore") !== "") why.push("the .gitignore entries were added again to an existing lakefile's folder");
  for (const [f, text] of [["lakefile.toml", 'name = "mine"\n'], ["lakefile.lean", "import Lake\n"]]) {
    reset();
    fs.writeFileSync(path.join(d, f), text);
    fs.writeFileSync(path.join(d, "lean-toolchain"), "leanprover/lean4:v4.0.0\n");
    const res = ed();
    if (res.userLakefile !== f || res.notes.length || read(d, f) !== text || read(d, "lean-toolchain") !== "leanprover/lean4:v4.0.0\n" || (f === "lakefile.lean" && fs.existsSync(path.join(d, "lakefile.toml"))))
      why.push(`a user's ${f} or its lean-toolchain was written`);
  }
  // whether a user's lakefile already requires "vts" at "out" (setup.sh's note only when it does not)
  for (const [f, text, want] of [
    ["lakefile.toml", 'name = "app"\n\n# editor support\n[[require]]\nname = "vts"\npath = ".vreact"\n', true],
    ["lakefile.toml", "name = 'app'\n[[require]]\nname = 'vts'\npath = './.vreact/'  # generated\n", true],
    ["lakefile.toml", 'name = "app"\n[[require]]\nname = "batteries"\npath = ".vreact"\n\n[[require]]\nname = "vts"\npath = "other"\n', false],
    ["lakefile.toml", 'name = "app"\n[[lean_lib]]\nname = "vts"\npath = ".vreact"\n', false],
    ["lakefile.lean", 'import Lake\nopen Lake DSL\npackage app\nrequire vts from ".vreact"\n', true],
    ["lakefile.lean", 'import Lake\nopen Lake DSL\npackage app\n-- require vts from ".vreact"\n', false],
    // (a require in a block comment is not one; one after a comment on its line is)
    ["lakefile.lean", 'import Lake\nopen Lake DSL\npackage app\n/- old: /- nested -/\nrequire vts from ".vreact"\n-/\n', false],
    ["lakefile.lean", 'import Lake\nopen Lake DSL\npackage app\n/- editor -/ require vts from ".vreact" -- the generated project\n', true],
  ] as [string, string, boolean][]) {
    reset();
    fs.writeFileSync(path.join(d, f), text);
    const res = ed();
    if (res.requiresOut !== want || res.notes.length) why.push(`requiresOut of ${JSON.stringify(text)}: ${res.requiresOut}`);
  }
  for (const [text, note] of [['name = "app"\n[[require]]\nname = "vts"\npath = ".vreact"\n', false], ['name = "app"\n', true]] as [string, boolean][]) {
    reset();
    fs.writeFileSync(path.join(d, "lakefile.toml"), text);
    const sp = spawnSync(process.execPath, ["--no-warnings", "--experimental-strip-types", path.join(here, "..", "src", "ide.ts"), d], { encoding: "utf8" });
    if (sp.status !== 0 || /kept your lakefile\.toml/.test(sp.stdout) !== note) why.push(`setup.sh's note for ${JSON.stringify(text)} (exit ${sp.status}): ${JSON.stringify(sp.stdout)}`);
  }
  reset();
  ed(".");
  if (fs.readdirSync(d).length) why.push(`"out": "." (the generated project is the folder) got editor files: ${fs.readdirSync(d).join(", ")}`);
  // setup.sh runs ide.ts as a script through the skill's `tool` symlink
  reset();
  fs.writeFileSync(path.join(d, "vreact.json"), '{ "out": "build/lean" }\n');
  const sp = spawnSync(process.execPath, ["--no-warnings", "--experimental-strip-types", path.join(here, "..", "skill", "verified-react", "tool", "src", "ide.ts"), d], { encoding: "utf8" });
  if (sp.status !== 0 || !lakefileOk(d, "build/lean") || read(d, "lean-toolchain") !== toolchain) why.push(`setup.sh's ide.ts step (exit ${sp.status}): ${sp.stdout}${sp.stderr}`);
  if (!why.length) ok("editor files: written fresh, idempotent, follow the library and \"out\", stale manifest removed, a user's lakefile.toml/lakefile.lean untouched (its require of \"vts\" recognized), setup.sh's script step and its note");
  else bad("editor files", why.join("; "));
}

// the report of doctored Lean output of a verified fixture never says VERIFIED (tests/honesty.ts)
console.log("report honesty (doctored Lean output)");
if (!only.length) honestyChecks(here, work, ok, bad);
console.log(`\n${failed === 0 ? "✔" : "✗"} ${passed} passed, ${failed} failed`);
process.exit(failed ? 1 : 0);
