/**
 * Synthesis regression: run `vreact synth` on small projects (tests/synth/…) and check what is
 * found, what is reported as proved, and what is written. `node tests/synth.test.ts [case…]`.
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { synthCommand, type SynthResult } from "../src/synth.ts";
import { loadConfig } from "../src/cli.ts";
import { translate } from "../src/module.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const fixtures = path.join(here, "synth", "fixtures");
const only = process.argv.slice(2);
let ok = true;
const check = (name: string, cond: boolean, msg = "") => {
  ok &&= cond;
  console.log(`${cond ? "✓" : "✗"} ${name}${msg ? "  " + msg : ""}`);
};

/** A fresh project in tests/.work/synth-<name>: the fixture's src/ (or the given files) and a tsconfig. */
function project(name: string, files?: Record<string, string>): string {
  const dir = path.join(here, ".work", `synth-${name}`);
  fs.rmSync(dir, { recursive: true, force: true });
  fs.mkdirSync(path.join(dir, "src"), { recursive: true });
  const fx = path.join(fixtures, name);
  const cfg = fs.existsSync(path.join(fx, "tsconfig.json")) ? path.join(fx, "tsconfig.json") : path.join(here, "todo", "tsconfig.json");
  fs.copyFileSync(cfg, path.join(dir, "tsconfig.json"));
  if (files) for (const [to, from] of Object.entries(files)) fs.copyFileSync(from, path.join(dir, to));
  else for (const f of fs.readdirSync(path.join(fx, "src"))) fs.copyFileSync(path.join(fx, "src", f), path.join(dir, "src", f));
  return dir;
}

/** Run synth, recording its console output and every write to the project's sources. */
async function synth(dir: string, file: string, opts: { write?: boolean; maxSize?: number } = {}) {
  const writes: string[] = [];
  const lines: string[] = [];
  const wfs = fs.writeFileSync;
  const log = console.log;
  (fs as { writeFileSync: unknown }).writeFileSync = (p: fs.PathOrFileDescriptor, ...rest: unknown[]) => {
    if (typeof p === "string" && path.resolve(p).startsWith(path.join(dir, "src"))) writes.push(path.relative(dir, p));
    return (wfs as (...a: unknown[]) => void)(p, ...rest);
  };
  console.log = (...a: unknown[]) => {
    lines.push(a.join(" "));
    log(...a);
  };
  let res: SynthResult[];
  try {
    res = await synthCommand(dir, [file], opts);
  } finally {
    (fs as { writeFileSync: unknown }).writeFileSync = wfs;
    console.log = log;
  }
  const by = (fn: string) => res.filter((r) => r.fn === fn);
  return { res, out: lines.join("\n"), writes, by };
}

const read = (dir: string, f: string) => fs.readFileSync(path.join(dir, f), "utf8");
const code = (text: string) => text.replace(/\/\/.*$/gm, "");
const solutions = (rs: SynthResult[]) => rs.map((r) => (r.proved ? r.solution : null));
const cases: Record<string, () => Promise<void>> = {
  // append / remove-by-key / update-by-key
  async cart() {
    const dir = project("cart", { "src/cart.ts": path.join(here, "synth", "cart.holes.ts") });
    const { res, writes } = await synth(dir, "src/cart.ts", { write: true });
    const expect: Record<string, RegExp> = {
      addItem: /\[\.\.\.c\.items, \{ id: c\.nextId, qty: 1 \}\].*nextId: c\.nextId \+ 1/,
      removeItem: /c\.items\.filter\(\(x\) => x\.id !== id\)/,
      bump: /c\.items\.map\(\(x\) => \(x\.id === id \? \{ \.\.\.x, qty: x\.qty \+ 1 \} : x\)\)/,
    };
    for (const r of res) check(`cart: ${r.fn}`, !!r.solution && r.proved && !!expect[r.fn]?.test(r.solution), r.solution ?? "(none)");
    check("cart: one write, at the end", writes.length === 1, writes.join(", "));
  },
  // parentheses, BOM, not exported, inline object params, optional field, early-return narrowing, preconditions
  async misc() {
    const dir = project("misc");
    const { by, out, writes } = await synth(dir, "src/misc.ts", { write: true });
    // (inc is a helper once it is filled: `inc(x)` is as good as `x + 1`)
    const want: Record<string, string[]> = { total: ["(base + 1)"], negSucc: ["(x + 1)"], inc: ["x + 1"], addX: ["a.x + b.y"], clearSel: ["{ ...s, selected: undefined }"], succ: ["x + 1", "inc(x)"], width: ["s.w"], bonus: ["points"] };
    for (const [fn, s] of Object.entries(want)) check(`misc: ${fn}`, s.includes(String(solutions(by(fn))[0])), String(solutions(by(fn))[0]));
    check("misc: never (vacuous) proved, with the reason it is untested", !!by("never")[0]?.proved && out.includes("no generated input satisfies the precondition of never"));
    const text = read(dir, "src/misc.ts");
    check("misc: byte-order mark kept", text.startsWith("\uFEFF"));
    check("misc: written with parentheses", text.includes("return (base + 1) * qty;") && text.includes("return -(x + 1);"));
    check("misc: no hole left, hole import dropped", !/\bhole\b/.test(code(text)));
    check("misc: written program translates", translate(loadConfig(dir)).ok);
    check("misc: one write", writes.length === 1, writes.join(", "));
  },
  // several holes in one function are filled and proved together
  async joint() {
    const dir = project("joint");
    const { by, out, writes } = await synth(dir, "src/joint.ts", { write: true });
    check("joint: bucket (both holes proved together)", JSON.stringify(solutions(by("bucket"))) === JSON.stringify(["0", "0"]), JSON.stringify(solutions(by("bucket"))));
    check("joint: step (one hole per case)", solutions(by("step")).every((s) => s === "{ ...s, ops: s.ops + 1 }") && by("step").length === 2, JSON.stringify(solutions(by("step"))));
    check("joint: cap (backtracks from hole 1 = xs)", JSON.stringify(solutions(by("cap"))) === JSON.stringify(["[]", "[]"]) && out.includes("Lean rejects"), JSON.stringify(solutions(by("cap"))));
    const proofs = out.split("\n").filter((l) => l.includes("✔ proved by Lean"));
    check("joint: only whole functions are reported proved", proofs.length === 3 && proofs.every((l) => / with /.test(l)), proofs.join(" | "));
    check("joint: one write", writes.length === 1);
  },
  // a failing obligation elsewhere: the postcondition is never checked, so nothing is proved or written
  async blocked() {
    const dir = project("blocked");
    const before = read(dir, "src/limits.ts");
    const { by, writes } = await synth(dir, "src/limits.ts", { write: true });
    const c = by("capped")[0];
    check("blocked: capped not proved", !!c && !c.proved && /did not check capped/.test(c.note ?? "") && /index/.test(c.note ?? ""), c?.note);
    const t = by("trustedCap")[0];
    check("blocked: @trusted function refused", !!t && !t.proved && t.status === "skipped" && t.note === "@trusted");
    check("blocked: nothing written", writes.length === 0 && read(dir, "src/limits.ts") === before);
  },
  async "blocked-dep"() {
    const dir = project("blocked-dep");
    const { by, writes } = await synth(dir, "src/limits.ts", { write: true });
    const c = by("capped")[0];
    check("blocked-dep: capped not proved (imported module fails)", !!c && !c.proved && /did not check/.test(c.note ?? "") && /model\.ts/.test(c.note ?? ""), c?.note);
    check("blocked-dep: nothing written", writes.length === 0);
  },
  // a contracted helper: only addTodo's own postconditions are tested on its result
  async helpers() {
    const dir = project("helpers");
    const { by, writes } = await synth(dir, "src/board.ts");
    check("helpers: addTodo uses the contracted helper", solutions(by("addTodo"))[0] === "{ ...b, todo: addIfAbsent(b.todo, x) }", String(solutions(by("addTodo"))[0]));
    check("helpers: dry run writes nothing", writes.length === 0);
  },
  // noUnusedLocals: the last fill would leave `hole` unused
  async unused() {
    const dir = project("unused");
    const { by } = await synth(dir, "src/inc.ts", { write: true });
    const text = read(dir, "src/inc.ts");
    check("unused: inc proved and written", solutions(by("inc"))[0] === "x + 1" && text.includes("return x + 1;"));
    check("unused: hole import dropped, project translates under noUnusedLocals", !/\bhole\b/.test(code(text)) && translate(loadConfig(dir)).ok);
  },
  // the path as typed in another letter case (case-insensitive file systems)
  async pathcase() {
    const dir = project("pathcase");
    if (!fs.existsSync(path.join(dir, "SRC", "limits.ts"))) return console.log("- pathcase: case-sensitive file system, skipped");
    const { by, writes } = await synth(dir, "SRC/limits.ts", { write: true });
    check("pathcase: Lean checks the right file (0, not x)", solutions(by("capped"))[0] === "0", String(solutions(by("capped"))[0]));
    check("pathcase: written to the real file", writes.length === 1 && writes[0] === path.join("src", "limits.ts") && read(dir, "src/limits.ts").includes("return 0;"), writes.join(", "));
  },
  // diagnostics: size reached and why the search stopped
  async nosolution() {
    const dir = project("nosolution");
    const { by, out, writes } = await synth(dir, "src/u.ts", { maxSize: 3 });
    check("nosolution: not proved", !by("impossible")[0]?.proved);
    check("nosolution: reports size and stop reason", out.includes("up to size 3; stopped: all candidates up to size 3 were tried") && out.includes("no candidate passed the tests") && !out.includes("strengthen"), out.split("\n").slice(-4).join(" | "));
    check("nosolution: nothing written", writes.length === 0);
  },
};

for (const [name, run] of Object.entries(cases)) {
  if (only.length && !only.includes(name)) continue;
  console.log(`\n── ${name}`);
  await run();
}
console.log(ok ? "\n✔ synthesis regression passed" : "\n✗ synthesis regression failed");
process.exit(ok ? 0 : 1);
