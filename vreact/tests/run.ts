/**
 * Regression suite: every case file starts with
 *   // expect: verified | fail <kind…> | reject <message substring>
 * `verified`/`fail` cases are checked together in one Lean build; `reject` cases
 * must be refused by the translator with the given message.
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { loadConfig, verify } from "../src/cli.ts";
import { translate } from "../src/module.ts";

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
      if (fails.length === 0 && comps.every((x) => x.status === "verified")) ok(c.name, `(${comps.length} component(s))`);
      else bad(c.name, `expected verified; failures: ${fails.map((f) => `${f.where} [${f.kind}] ${f.desc}\n${f.lean}`).join("\n")} ${comps.map((x) => x.status).join(",")}`);
    } else {
      const want = c.expect.slice(1).sort();
      if (JSON.stringify(kinds) === JSON.stringify(want)) ok(c.name, `fails as expected: ${kinds.join(", ")}`);
      else bad(c.name, `expected failures [${want.join(", ")}], got [${kinds.join(", ")}] ${fails.map((f) => f.where + " " + f.desc).join("; ")}`);
    }
  }
  console.log(`  (${r.obligations.total} obligations in the batch: ${r.obligations.proved} proved, ${r.obligations.failed} failed)`);
}
console.log(`\n${failed === 0 ? "✔" : "✗"} ${passed} passed, ${failed} failed`);
process.exit(failed ? 1 : 0);
