/**
 * Synthesis regression: run `vreact synth` on small projects (tests/synth/…) and check what is
 * found, what is reported as proved, and what is written. `node tests/synth.test.ts [case…]`.
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import ts from "typescript";
import { synthCommand, mayShareExecution, canonical, type SynthResult } from "../src/synth.ts";
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
    // capped uses first, whose index obligation fails: its proof rests on that sorry
    const c = by("capped")[0];
    check("blocked: capped not proved", !!c && !c.proved && /sorry/.test(c.note ?? ""), c?.note);
    // an unrelated failure in the same file does not keep low from being checked
    check("blocked: independent low proved", solutions(by("low"))[0] === "0", String(solutions(by("low"))[0]));
    const t = by("trustedCap")[0];
    check("blocked: @trusted function refused", !!t && !t.proved && t.status === "skipped" && t.note === "@trusted");
    const after = read(dir, "src/limits.ts");
    check("blocked: only low written", writes.length === 1 && after !== before && /function low[\s\S]*?return 0;/.test(after) && /function capped[\s\S]*?return hole<int>\(\);/.test(after) && /function trustedCap[\s\S]*?return hole<int>\(\);/.test(after));
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
  // N25: holes no call shares (switch cases) are searched once each; a hole without candidates
  // backjumps over the holes it does not depend on (before: 3^(n-1) searches of the last hole)
  async "Sx-joint5"() {
    const dir = project("Sx-joint5");
    const t0 = Date.now();
    const { by, out } = await synth(dir, "src/r.ts", { maxSize: 5 });
    const secs = (Date.now() - t0) / 1000;
    const headers = (fn: string, k: number) => out.split("\n").filter((l) => l.startsWith(`hole ${k}/5 in ${fn}:`)).length;
    check("Sx-joint5: step not proved", by("step").length === 5 && by("step").every((r) => !r.proved));
    check("Sx-joint5: each hole of step searched once", [1, 2, 3, 4, 5].every((k) => headers("step", k) === 1), [1, 2, 3, 4, 5].map((k) => headers("step", k)).join(","));
    check("Sx-joint5: backjump over the independent holes", out.includes("hole 5 fails whatever the fill of holes 1, 2, 3, 4"));
    check("Sx-joint5: no Lean check for step", !/Lean rejects|proved by Lean: step with/.test(out));
    check("Sx-joint5: step5 proved together, each hole searched once", by("step5").length === 5 && by("step5").every((r) => r.proved) && [1, 2, 3, 4, 5].every((k) => headers("step5", k) === 1), JSON.stringify(solutions(by("step5"))));
    // a dependent pair: hole 2 is searched with hole 1's fill in its tests
    check("Sx-joint5: twice (hole 2 depends on hole 1)", JSON.stringify(solutions(by("twice"))) === JSON.stringify(["x", "(1 + 1)"]) && out.includes("hole 2/2 in twice (with hole 1 = x)"), JSON.stringify(solutions(by("twice"))));
    check("Sx-joint5: within the time budget", secs < 5 * 60, `${secs.toFixed(0)}s`);
  },
  // which holes a call can evaluate together (the basis of the search reuse above)
  async "Sx-shared"() {
    const holesOf = (src: string) => {
      const sf = ts.createSourceFile("t.ts", src, ts.ScriptTarget.ES2022, true);
      const fn = sf.statements.find(ts.isFunctionDeclaration)!;
      const hs: ts.Node[] = [];
      const visit = (n: ts.Node) => {
        if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === "hole") hs.push(n);
        ts.forEachChild(n, visit);
      };
      visit(fn);
      return { fn, hs };
    };
    const shared = (src: string) => {
      const { fn, hs } = holesOf(src);
      return mayShareExecution(hs[0], hs[1], fn, false);
    };
    const cases: [string, string, boolean][] = [
      ["switch cases", `function f(a: A) { switch (a.kind) { case "a": return hole(); case "b": { const y = 1; return hole(); } } }`, false],
      ["if / else", `function f(c: boolean) { if (c) { return hole(); } else { return hole(); } }`, false],
      ["early return", `function f(c: boolean) { if (c) return hole(); return hole(); }`, false],
      ["early return after a local", `function f(c: boolean) { if (c) { const y = hole(); return y; } return hole(); }`, false],
      ["ternary", `function f(c: boolean) { return c ? hole() : hole(); }`, false],
      ["sequence", `function f(x: int) { const y = hole(); return y + hole(); }`, true],
      ["if without return", `function f(c: boolean) { let y = 0; if (c) { y = hole(); } return y + hole(); }`, true],
      ["both in one lambda", `function f(xs: X[]) { return xs.map((x) => (x.c ? hole() : hole())); }`, true],
      ["in a loop", `function f(xs: X[]) { let s = 0; for (const x of xs) { if (x.c) { s = hole(); } else { s = hole(); } } return s; }`, true],
      ["a closure called later", `function f(c: boolean) { const g = () => hole(); return c ? g() : hole(); }`, true],
      ["a return of a nested lambda", `function f(c: boolean, xs: X[]) { const ys = xs.map((x) => { return hole(); }); return c ? ys : hole(); }`, true],
      ["condition and branch", `function f() { if (hole()) return hole(); return 0; }`, true],
    ];
    for (const [name, src, want] of cases) check(`Sx-shared: ${name}`, shared(src) === want, `got ${shared(src)}`);
    const { fn, hs } = holesOf(`function f(c: boolean) { if (c) return hole(); return hole(); }`);
    check("Sx-shared: a recursive function shares everything", mayShareExecution(hs[0], hs[1], fn, true));
  },
  // P78: the scope has the translator's narrowing (complement of a test included)
  async "Sx-narrowing"() {
    const dir = project("Sx-narrowing");
    const { by, out } = await synth(dir, "src/List.ts");
    const want: Record<string, string> = { width2: "s.w", w4: "s.w + 1", w6: "s.h + s.w", w7: "k + s.h", triX: "0" };
    for (const [fn, s] of Object.entries(want)) check(`Sx-narrowing: ${fn}`, solutions(by(fn))[0] === s, String(solutions(by(fn))[0]));
    check("Sx-narrowing: early return narrows s to rect", out.includes("hole in width2: int   scope: s, s.w, s.h"));
    check("Sx-narrowing: two variants left: shared fields only", out.includes("hole in triX: int   scope: t\n"));
  },
  // N26: a field (and a parameter) spelled `hole` is not a use of the imported hole
  async "Sx-holefield"() {
    const dir = project("Sx-holefield");
    const { by, out } = await synth(dir, "src/golf.ts", { write: true });
    const text = read(dir, "src/golf.ts");
    const s = solutions(by("nextHole"))[0];
    check("Sx-holefield: nextHole proved", s === "{ ...c, hole: c.hole + 1 }" || s === "{ ...c, hole: after(c.hole) }", String(s));
    check("Sx-holefield: no candidate failed to translate", !out.includes("does not translate"));
    check("Sx-holefield: hole import dropped, field kept, translates under noUnusedLocals", /import \{ ensures, type int \} from "vreact\/spec";/.test(text) && text.includes("readonly hole: int") && translate(loadConfig(dir)).ok);
  },
  // N27: diagnostics — untranslatable candidates are not Lean rejections; a contract calling
  // an unfinished function is reported as such
  async "Sx-diag"() {
    const dir = project("Sx-diag");
    const { by, out } = await synth(dir, "src/d.ts", { maxSize: 4 });
    const part = (fn: string) => out.slice(out.indexOf(`hole in ${fn}`)).split("\nhole in ")[0];
    check("Sx-diag: clearSel not proved", !by("clearSel")[0]?.proved);
    check("Sx-diag: clearSel: candidates do not translate, Lean never ran", part("clearSel").includes("do not translate") && !/Lean rejects|accept candidates that Lean rejects/.test(part("clearSel")), part("clearSel").split("\n").slice(-1)[0]);
    const p = by("plusSq")[0];
    check("Sx-diag: plusSq: the contract depends on unfinished sq", !!p && !p.proved && p.tested === 0 && /contract of plusSq depends on unfinished function sq/.test(p.note ?? "") && !part("plusSq").includes("postcondition fails"), p?.note);
    check("Sx-diag: viaStub: the contract cannot be evaluated (not 'postcondition fails')", /contract of viaStub runs into a hole/.test(part("viaStub")) && !part("viaStub").includes("postcondition fails") && !part("viaStub").includes("the random tests accept"), part("viaStub").split("\n").slice(-1)[0]);
  },
  // N28: a proof relative to @trusted declarations has its own status and lists what it assumes
  async "Sx-relative"() {
    const dir = project("Sx-relative");
    const { by } = await synth(dir, "src/t.ts", { write: true });
    const v = by("viaStub")[0];
    check("Sx-relative: viaStub proved relative to stub", !!v && v.proved && v.status === "proved-relative" && JSON.stringify(v.relative_to) === JSON.stringify(["VTS.t.stub", "VTS.t.stub.post"]), JSON.stringify(v));
    const i = by("inc")[0];
    check("Sx-relative: inc proved outright", !!i && i.proved && i.status === "proved" && i.relative_to === undefined, JSON.stringify(i));
    check("Sx-relative: written", read(dir, "src/t.ts").includes("return stub(x);"));
  },
  // N29: the same candidate (up to whitespace and parentheses) goes to Lean once
  async "Sx-dedup"() {
    check("Sx-dedup: parentheses and spacing are ignored", canonical("(a + b) + 1") === canonical("a + b  + 1") && canonical("{ ...s, f: (x) }") === canonical("{ ...s, f: x }") && canonical("xs.map((x) => x.k)") === canonical("xs.map(x => x.k)"));
    check("Sx-dedup: different trees stay different", canonical("a + (b + 1)") !== canonical("a + b + 1") && canonical("!x") !== canonical("-x") && canonical('"a"') !== canonical('"b"'));
    const dir = project("Sx-dedup");
    const { by, out } = await synth(dir, "src/f.ts");
    const checked = out.split("\n").filter((l) => /^ {2}(✗ Lean rejects|✔ proved by Lean)/.test(l)).map((l) => canonical(l.replace(/^ {2}(✗ Lean rejects |✔ proved by Lean: )/, "").replace(/: postcondition.*$/, "")));
    check("Sx-dedup: no candidate checked twice", checked.length >= 2 && new Set(checked).size === checked.length, `${checked.length} checks`);
    check("Sx-dedup: above proved", solutions(by("above"))[0] === "a + b + 1 + 1", String(solutions(by("above"))[0]));
  },
};

for (const [name, run] of Object.entries(cases)) {
  if (only.length && !only.includes(name)) continue;
  console.log(`\n── ${name}`);
  await run();
}
console.log(ok ? "\n✔ synthesis regression passed" : "\n✗ synthesis regression failed");
process.exit(ok ? 0 : 1);
