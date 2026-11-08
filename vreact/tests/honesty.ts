/**
 * Report honesty: the fixture `tests/honesty/` is verified once with Lean; then Lean's
 * output is doctored (an error, a module not built, a missing or forged `#print axioms`
 * report, `sorryAx`, `VReact.assumed`, a foreign axiom, a missing or forged sentinel, a sorry
 * warning, a failed build without messages, …) and the report of the doctored output must
 * never say VERIFIED — neither the verdict nor the items the doctoring concerns.
 */
import fs from "node:fs";
import path from "node:path";
import { loadConfig, reportFrom, type Report } from "../src/cli.ts";
import { translate } from "../src/module.ts";
import { runLake, lakeMessages } from "../src/lean.ts";

type Check = (r: Report) => string[];

export function honestyChecks(here: string, work: string, ok: (name: string, msg?: string) => void, bad: (name: string, msg: string) => void) {
  const src = path.join(here, "honesty");
  const dir = path.join(work, "honesty");
  fs.rmSync(path.join(dir, "src"), { recursive: true, force: true });
  fs.rmSync(path.join(dir, "proofs"), { recursive: true, force: true });
  fs.mkdirSync(dir, { recursive: true });
  fs.cpSync(path.join(src, "src"), path.join(dir, "src"), { recursive: true });
  fs.cpSync(path.join(src, "proofs"), path.join(dir, "proofs"), { recursive: true });
  fs.copyFileSync(path.join(here, "todo", "tsconfig.json"), path.join(dir, "tsconfig.json"));
  const cfg = loadConfig(dir);
  const tr = translate(cfg);
  if (!tr.ok) return bad("honesty fixture", [...tr.tsDiagnostics, ...tr.errors.map((e) => e.message)].join(" | "));
  const lk = runLake(cfg.outDir, cfg.leanLib);
  const report = (raw: string, status = 0) => reportFrom(cfg, tr, lakeMessages(raw, status)).report;
  const base = report(lk.raw, lk.status);
  if (base.verdict !== "verified" || !base.ok) return bad("honesty fixture", `expected the fixture to verify, got ${base.verdict}: ${base.errors.join(" | ")} ${base.notChecked.map((n) => n.reason).join(" | ")}`);

  // positions in the generated files
  const DEFS = path.join("VTS", "model", "Defs.lean");
  const VIEW = path.join("VTS", "App", "View.lean");
  const lines = (rel: string) => fs.readFileSync(path.join(cfg.outDir, rel), "utf8").split("\n");
  const lineOf = (rel: string, re: RegExp) => {
    const i = lines(rel).findIndex((l) => re.test(l));
    if (i < 0) throw new Error(`honesty: no line ${re} in ${rel}`);
    return i + 1;
  };
  const markerAt = (rel: string, after: RegExp) => {
    const ls = lines(rel);
    const from = lineOf(rel, after) - 1;
    for (let i = from; i < ls.length; i++) {
      const c = ls[i].indexOf("/-⟦ob");
      if (c >= 0) return { line: i + 1, col: [...ls[i].slice(0, c)].length };
    }
    throw new Error(`honesty: no marker after ${after}`);
  };
  const raw = lk.raw;
  const drop = (re: RegExp) => (s: string) => s.split("\n").filter((l) => !re.test(l)).join("\n");
  const add = (...extra: string[]) => (s: string) => s + "\n" + extra.join("\n") + "\n";
  const replace = (re: RegExp, by: string) => (s: string) => {
    if (!re.test(s)) throw new Error(`honesty: ${re} not in lake's output`);
    return s.replace(re, by);
  };
  const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const axLine = (q: string) => new RegExp(`^info: ${esc(DEFS.split(path.sep).join("/"))}:\\d+:\\d+: '${esc(q)}' .*$`, "m");
  const defsP = DEFS.split(path.sep).join("/");
  const viewP = VIEW.split(path.sep).join("/");
  const incDef = lineOf(DEFS, /def inc /);
  const showRender = lineOf(VIEW, /^namespace Show$/) + lines(VIEW).slice(lineOf(VIEW, /^namespace Show$/)).findIndex((l) => /^def render /.test(l)) + 1;
  const incPost = markerAt(DEFS, /^theorem inc\.post/);
  const printInc = lineOf(DEFS, /^#print axioms VTS\.model\.inc$/);
  // `vreact_ob`'s result for inc's postcondition: at its token, 13 columns after the marker
  const incOb = `${defsP}:${incPost.line}:${incPost.col + 13}`;
  const incOk = new RegExp(`^info: ${esc(incOb)}: vreact:ok$`, "m");
  if (!incOk.test(raw)) throw new Error(`honesty: no vreact:ok for inc's postcondition at ${incOb}`);

  /** the report must not say VERIFIED, and the named items must not be verified */
  const never = (...names: string[]): Check => (r) => {
    const why: string[] = [];
    if (r.verdict === "verified" || r.ok) why.push(`verdict ${r.verdict}`);
    const all = [...r.components, ...r.functions, ...r.constants, ...r.certificates.map((c) => ({ ...c, name: c.name + ".certificate" }))];
    for (const n of names) {
      const it = all.find((x) => x.name === n);
      if (!it) why.push(`no item ${n}`);
      else if (it.status === "verified") why.push(`${n} is verified`);
    }
    return why;
  };
  const and = (...cs: Check[]): Check => (r) => cs.flatMap((c) => c(r));
  const expect = (what: string, get: (r: Report) => unknown, want: unknown): Check => (r) => (get(r) === want ? [] : [`${what}: expected ${want}, got ${get(r)}`]);
  const proved = (n: number) => expect("proved", (r) => r.obligations.proved, n);
  const verdict = (v: Report["verdict"]) => expect("verdict", (r) => r.verdict, v);
  const status = (name: string, s: string) => expect(name, (r) => [...r.components, ...r.functions, ...r.constants].find((x) => x.name === name)?.status, s);
  const total = base.obligations.total;

  const cases: [string, (s: string) => string, Check, number?][] = [
    // (inc's axioms look clean although its declaration failed: something else stands in for
    // it, so App, which uses inc, is not verified either, and none of their obligations count)
    ["an error in a generated declaration (no marker)", add(`error: ${defsP}:${incDef}:0: injected error`), and(never("inc", "App", "App.certificate"), verdict("not-verified"), status("Show", "verified"), (r) => (r.notChecked.some((u) => u.desc.includes("postcondition of inc")) ? [] : ["inc's postcondition counted as proved"]))],
    ["an error in a child component's render (no marker)", add(`error: ${viewP}:${showRender}:0: injected error`), and(never("Show", "App", "App.certificate"), verdict("not-verified"), status("inc", "verified"))],
    ["an error at an obligation's marker", add(`error: ${defsP}:${incPost.line}:${incPost.col}: injected failure`), and(never("inc"), verdict("not-verified"), expect("failed", (r) => r.obligations.failed, 1))],
    ["an error with a ./ path", add(`error: ./${defsP}:${incPost.line}:${incPost.col}: injected failure`), and(never("inc"), expect("failed", (r) => r.obligations.failed, 1))],
    ["an error in a user proof", add(`error: Proofs/Base.lean:2:0: injected error`), and(never(), verdict("not-verified"))],
    ["a lake error without position", add(`error: build cycle detected:`), and(never(), verdict("not-verified"))],
    ["a failed build without any message", (s) => s.split("\n").filter((l) => !/^error/.test(l)).join("\n"), and(never(), verdict("not-verified")), 1],
    ["a module not built (no output for VTS.App.View)", drop(new RegExp(`${esc(viewP)}|VTS\\.App\\.View`)), and(never("App", "Show", "App.certificate"), proved(3))],
    ["a missing #print axioms report", drop(axLine("VTS.model.inc")), and(never("inc"), status("inc", "unchecked"))],
    ["a forged report from a user proof (real one dropped)", (s) => add(`info: Proofs/Base.lean:2:0: 'VTS.model.inc' does not depend on any axioms`)(drop(axLine("VTS.model.inc"))(s)), and(never("inc"), status("inc", "unchecked"))],
    ["a forged report at another line of the generated file", (s) => add(`info: ${defsP}:${incDef}:0: 'VTS.model.inc' does not depend on any axioms`)(drop(axLine("VTS.model.inc"))(s)), and(never("inc"), status("inc", "unchecked"))],
    ["a forged report for inc at the #print line of another name", (s) => add(`info: ${defsP}:${printInc + 1}:0: 'VTS.model.inc' does not depend on any axioms`)(drop(axLine("VTS.model.inc"))(s)), and(never("inc"), status("inc", "unchecked"))],
    ["sorryAx in a report", replace(/'VTS\.model\.inc\.post' depends on axioms: \[propext\]/, "'VTS.model.inc.post' depends on axioms: [propext, sorryAx]"), and(never("inc"), status("inc", "incomplete"), verdict("incomplete"))],
    ["a second, clean report after one with sorryAx", (s) => add(`info: ${defsP}:${printInc + 1}:0: 'VTS.model.inc.post' depends on axioms: [propext]`)(replace(/'VTS\.model\.inc\.post' depends on axioms: \[propext\]/, "'VTS.model.inc.post' depends on axioms: [propext, sorryAx]")(s)), and(never("inc"), status("inc", "incomplete"))],
    ["VReact.assumed in a report", replace(/'VTS\.model\.inc\.post' depends on axioms: \[propext\]/, "'VTS.model.inc.post' depends on axioms: [propext, VReact.assumed]"), and(never("inc"), status("inc", "assumes"), verdict("verified-modulo-trusted"))],
    ["an axiom declared outside the translation (even in VTS.)", replace(/'VTS\.model\.inc\.post' depends on axioms: \[propext\]/, "'VTS.model.inc.post' depends on axioms: [propext, VTS.model.helper]"), and(never("inc"), status("inc", "trusted"))],
    ["a missing sentinel", drop(new RegExp(`^info: ${esc(defsP)}:\\d+:\\d+: "vreact:checked"`)), and(never("inc", "clamp"), proved(total - 3), verdict("incomplete"))],
    ["a forged sentinel (real one dropped)", (s) => add(`info: ${defsP}:${incDef}:0: "vreact:checked"`, `info: Proofs/Base.lean:2:0: "vreact:checked"`)(drop(new RegExp(`^info: ${esc(defsP)}:\\d+:\\d+: "vreact:checked"`))(s)), and(never("inc", "clamp"), proved(total - 3))],
    ["a sorry warning", add(`warning: ${defsP}:${incDef}:0: declaration uses 'sorry'`), and(never("inc"), verdict("incomplete"))],
    // `vreact_ob`'s evidence (see VReact/Budget.lean): an obligation is proved only with a
    // `vreact:ok` of its own at its marker and no failure there
    ["a missing vreact:ok", drop(incOk), and(never("inc"), proved(total - 1), expect("unchecked", (r) => r.obligations.unchecked, 1), (r) => (r.notChecked.some((u) => u.desc.includes("postcondition of inc") && u.reason.includes("vreact:ok")) ? [] : ["inc's postcondition not reported as unchecked for want of vreact:ok"]))],
    ["a warning-severity failure (vreact_ob admitted the goal) instead of vreact:ok", (s) => drop(incOk)(s) + `\nwarning: ${incOb}: vreact: \`grind\` failed\n⊢ False\nwarning: ${defsP}:${lineOf(DEFS, /^theorem inc\.post/)}:0: declaration uses 'sorry'\n`, and(never("inc"), verdict("not-verified"), expect("failed", (r) => r.obligations.failed, 1), status("clamp", "verified"))],
    ["a failure next to the real vreact:ok (a forged result from a simproc inside the obligation)", add(`warning: ${incOb}: vreact: injected failure`), and(never("inc"), verdict("not-verified"), expect("failed", (r) => r.obligations.failed, 1))],
    ["a forged vreact:ok from a user proof (real one dropped)", (s) => add(`info: Proofs/Base.lean:${incPost.line}:${incPost.col + 13}: vreact:ok`, `info: Proofs/Base.lean:2:0: vreact:ok`)(drop(incOk)(s)), and(never("inc"), proved(total - 1))],
    ["a forged vreact:ok at another position of the generated file (real one dropped)", (s) => add(`info: ${defsP}:${incDef}:0: vreact:ok`, `info: ${defsP}:${incPost.line}:${incPost.col + 60}: vreact:ok`)(drop(incOk)(s)), and(never("inc"), proved(total - 1))],
    ["a vreact failure warning at no marker of a generated file", add(`warning: ${defsP}:${incDef}:0: vreact: injected failure`), and(never("inc"), verdict("not-verified"))],
    ["sorryAx that no failure explains", replace(/'VTS\.model\.inc\.post' depends on axioms: \[propext\]/, "'VTS.model.inc.post' depends on axioms: [propext, sorryAx]"), and(never("inc"), proved(total - 1), (r) => (r.notChecked.some((u) => u.desc.includes("postcondition of inc") && u.reason.includes("sorryAx")) ? [] : ["inc's postcondition counted as proved although its axioms have an unexplained sorryAx"]))],
  ];
  let n = 0;
  for (const [name, mutate, check, st] of cases) {
    let why: string[];
    try {
      why = check(report(mutate(raw), st ?? 0));
    } catch (e) {
      why = [String(e)];
    }
    if (why.length) bad(`honesty: ${name}`, why.join("; "));
    else n++;
  }
  if (n === cases.length) ok(`honesty: ${n} kinds of doctored Lean output, none reported as VERIFIED`);
}
