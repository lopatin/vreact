/** Running Lean on the generated project and mapping results back to TypeScript. */
import { spawnSync } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import type { Obligation } from "./ctx.ts";

export interface LeanMessage {
  severity: "error" | "warning" | "info";
  /** path relative to the generated project; "" for lake errors that name no file */
  file: string;
  /** 0 when Lean/Lake gave no position */
  line: number;
  col: number;
  text: string;
  /** the generated declaration the message lies in (set by `judge`) */
  decl?: string | null;
  /** classification of an unattributed error (set by `judge`) */
  cause?: ErrorCause;
  /**
   * an error about the whole file (a generated module the kernel re-check did not certify,
   * `runLake`): every declaration in it is broken; not itself listed (its cause is)
   */
  wholeFile?: boolean;
}

/**
 * Why an error could not be attributed to one obligation:
 * build — lake/import/lakefile problems (no or header position); proof — in a user proof file;
 * timeout — a declaration ran out of heartbeats / recursion depth outside an obligation;
 * follow-on — a later use of a declaration that failed above; internal — anything else
 * in generated Lean (translator bug or unsupported pattern).
 */
export type ErrorCause = "build" | "proof" | "timeout" | "follow-on" | "internal";

export interface Marker {
  id: number;
  file: string;
  line: number;
  col: number;
}

export function leanBin(): string {
  const elan = path.join(os.homedir(), ".elan", "bin");
  return fs.existsSync(path.join(elan, "lake")) ? elan : "";
}

/** A command of a user proof file that the whitelist rejects (`lean/ProofCheck.lean`). */
export interface ProofIssue {
  /** the file's path relative to the proofs directory */
  file: string;
  line: number;
  col: number;
  msg: string;
}

/** An import of a user proof file's header, as Lean's parser reads it (`lean/ProofCheck.lean`). */
export interface ProofImport {
  /** the module: its components joined by `.` (`«VTS».m.Defs` is `VTS.m.Defs`); a component
   * that itself contains a `.` stays escaped (`VTS.«m.Defs»`), naming no module of the project */
  name: string;
  /** the name's components, unescaped */
  parts: string[];
  /** where the module name is (1-based) */
  line: number;
  col: number;
}

/** The result of `checkProofFiles`. */
export interface ProofCheck {
  issues: ProofIssue[];
  /** each file's imports (by its path relative to the proofs directory, `/`-separated) */
  imports: Map<string, ProofImport[]>;
}

/** Libraries this process has built (`buildLeanLib`). */
const builtLibs = new Set<string>();

/**
 * Build the VReact library and vreact's Lean programs (`vreact-proofcheck`, `vreact-certify`)
 * once per process (lake is quick when they are up to date); returns the environment to run
 * them in (Lake's shared artifact cache off: see `runLake`).
 */
function buildLeanLib(leanLib: string): NodeJS.ProcessEnv {
  const bin = leanBin();
  const env = { ...process.env, PATH: bin ? `${bin}:${process.env.PATH}` : process.env.PATH, LAKE_ARTIFACT_CACHE: "false" };
  if (builtLibs.has(leanLib)) return env;
  const build = spawnSync("lake", ["build"], { cwd: leanLib, env, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
  if (build.error) throw new Error(`could not run lake (is Lean installed? see SKILL.md): ${build.error.message}`);
  if (build.status !== 0) throw new Error(`could not build the VReact Lean library in ${leanLib}:\n${((build.stdout ?? "") + (build.stderr ?? "")).trim().split("\n").slice(-12).join("\n")}`);
  builtLibs.add(leanLib);
  return env;
}

/** Results of `checkProofFiles` by input (the check runs Lean: `vreact synth` translates often). */
const proofCheckCache = new Map<string, ProofCheck>();

/**
 * The whitelist check of user proof files, before Lean elaborates them (they are imported by
 * the generated files, so whatever they declare — syntax, instances, options, code — takes
 * effect while the translation is checked). Runs `vreact-proofcheck` (`lean/ProofCheck.lean`),
 * which parses each file with Lean's parser and accepts only lemma-like commands; the library
 * (and the checker) are built first if needed. Also returns every file's imports as Lean's
 * parser reads them: vreact never reads a proof file's imports from its text (an escaped name
 * `«VTS».m.Defs`, a `/-` inside a line comment, a name on the line after `import`).
 */
export function checkProofFiles(leanLib: string, files: { name: string; text: string }[]): ProofCheck {
  if (!files.length) return { issues: [], imports: new Map() };
  // (in a fixed order: one result for one set of files, however they were listed)
  const sorted = [...files].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  const input = JSON.stringify(sorted);
  const cached = proofCheckCache.get(input);
  if (cached) return cached;
  const env = buildLeanLib(leanLib);
  const exe = path.join(leanLib, ".lake", "build", "bin", "vreact-proofcheck");
  const r = spawnSync("lake", ["env", exe], { cwd: leanLib, env, input, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
  if (r.error) throw new Error(`could not run the proof file check ${exe}: ${r.error.message}`);
  let out: ProofCheck | null = null;
  try {
    out = proofCheckResult(JSON.parse(r.stdout ?? ""), sorted.map((f) => f.name));
  } catch {
    out = null;
  }
  // never "no objections" from a check that did not run to the end
  if (r.status !== 0 || out === null) throw new Error(`the proof file check failed (exit ${r.status}${r.signal ? `, ${r.signal}` : ""}):\n${((r.stdout ?? "") + (r.stderr ?? "")).trim().split("\n").slice(-12).join("\n")}`);
  proofCheckCache.set(input, out);
  return out;
}

/** The output of `vreact-proofcheck` (`{issues, imports}`), checked to be complete: null otherwise. */
function proofCheckResult(parsed: unknown, names: string[]): ProofCheck | null {
  if (typeof parsed !== "object" || parsed === null) return null;
  const { issues, imports } = parsed as { issues?: unknown; imports?: unknown };
  if (!Array.isArray(issues) || typeof imports !== "object" || imports === null) return null;
  const byFile = new Map<string, ProofImport[]>();
  for (const name of names) {
    const list = (imports as Record<string, unknown>)[name];
    if (!Array.isArray(list)) return null;
    const out: ProofImport[] = [];
    for (const i of list as unknown[]) {
      const { name: parts, line, col } = (i ?? {}) as { name?: unknown; line?: unknown; col?: unknown };
      if (!Array.isArray(parts) || !parts.length || !parts.every((x) => typeof x === "string") || typeof line !== "number" || typeof col !== "number") return null;
      const ps = parts as string[];
      out.push({ name: ps.map((x) => (x.includes(".") ? `«${x}»` : x)).join("."), parts: ps, line, col });
    }
    byFile.set(name, out);
  }
  return { issues: issues as ProofIssue[], imports: byFile };
}

/** A Lean module of the generated project: generated (`VTS…`) or a user proof (`Proofs…`). */
interface ProjectModule {
  name: string;
  /** its source, relative to the project (`VTS/m/Defs.lean`) */
  rel: string;
  text: string;
  /** the modules it imports */
  imports: string[];
}

/** `VTS/m/Defs.lean` → `VTS.m.Defs` (and back): lake's module names, without Lean's `«…»` escapes. */
const modOfRel = (rel: string) => rel.replace(/\.lean$/, "").split(/[\\/]/).join(".");
const relOfMod = (mod: string) => mod.split(".").join("/") + ".lean";

/**
 * The modules a generated Lean file's header imports (the generator writes one plain `import` per
 * line). Not for proof files, whose imports come from Lean's parser (`checkProofFiles`).
 */
function headerImports(text: string): string[] {
  const code = text.replace(/\/-[\s\S]*?-\//g, " ").replace(/--.*$/gm, "");
  const out: string[] = [];
  for (const line of code.split("\n")) {
    const m = /^\s*import\s+(.*)$/.exec(line);
    if (m) out.push(...m[1].trim().split(/\s+/).filter(Boolean).map((x) => x.replace(/[«»]/g, "")));
    else if (line.trim()) break;
  }
  return out;
}

/**
 * The generated modules and the user proofs of a generated project: a proof file's imports as
 * Lean's parser reads them (`checkProofFiles`, whose result for the files the translation checked
 * is cached), never from its text, which a `/-` in a line comment, an escaped name `«VTS».m.Defs`
 * or a line break after `import` can make read otherwise.
 */
function projectModules(outDir: string, leanLib: string): ProjectModule[] {
  const out: ProjectModule[] = [];
  const add = (rel: string) => {
    const text = fs.readFileSync(path.join(outDir, rel), "utf8");
    out.push({ name: modOfRel(rel), rel: rel.split(path.sep).join("/"), text, imports: headerImports(text) });
  };
  const walk = (dir: string) => {
    const d = path.join(outDir, dir);
    if (!fs.existsSync(d)) return;
    for (const f of fs.readdirSync(d).sort()) {
      const rel = path.join(dir, f);
      if (fs.statSync(path.join(outDir, rel)).isDirectory()) walk(rel);
      else if (f.endsWith(".lean")) add(rel);
    }
  };
  if (fs.existsSync(path.join(outDir, "VTS.lean"))) add("VTS.lean");
  walk("VTS");
  walk("Proofs");
  const proofs = out.filter((m) => m.rel.startsWith("Proofs/"));
  const parsed = checkProofFiles(leanLib, proofs.map((m) => ({ name: m.rel.slice("Proofs/".length), text: m.text }))).imports;
  for (const m of proofs) m.imports = (parsed.get(m.rel.slice("Proofs/".length)) ?? []).map((i) => i.name);
  return out;
}

const sha256 = (data: string | Buffer) => crypto.createHash("sha256").update(data).digest("hex");

/** The files of a directory tree (relative paths); null if it holds anything but files and directories (a link, …). */
function treeFiles(root: string): string[] | null {
  const out: string[] = [];
  let odd = false;
  const walk = (rel: string) => {
    for (const f of fs.readdirSync(path.join(root, rel))) {
      const r = rel ? path.join(rel, f) : f;
      const st = fs.lstatSync(path.join(root, r));
      if (st.isDirectory()) walk(r);
      else if (st.isFile()) out.push(r);
      else odd = true;
    }
  };
  walk("");
  return odd ? null : out.sort();
}

/**
 * What the library and the toolchain contribute to every module's build: the toolchain, the
 * library's built modules and the project's lakefile. A module's key (`moduleKeys`) changes
 * with any of them.
 */
function libraryFingerprint(leanLib: string, outDir: string): string {
  const h = crypto.createHash("sha256");
  h.update(fs.readFileSync(path.join(leanLib, "lean-toolchain")));
  for (const f of ["lakefile.toml", "lean-toolchain"]) {
    const p = path.join(outDir, f);
    h.update(f + "\0" + (fs.existsSync(p) ? fs.readFileSync(p, "utf8") : "") + "\0");
  }
  const lib = path.join(leanLib, ".lake", "build", "lib", "lean");
  for (const f of treeFiles(lib) ?? []) if (/^VReact\b/.test(f) && f.endsWith(".olean")) h.update(f + "\0").update(fs.readFileSync(path.join(lib, f)));
  return h.digest("hex");
}

/**
 * A key of everything a module's Lean run depends on: its source, the keys of the project
 * modules it imports, and the library/toolchain fingerprint. Lean is deterministic, so two runs
 * with one key print the same messages.
 */
function moduleKeys(mods: ProjectModule[], fingerprint: string): Map<string, string> {
  const byName = new Map(mods.map((m) => [m.name, m]));
  const keys = new Map<string, string>();
  const key = (m: ProjectModule, seen: Set<string>): string => {
    const k = keys.get(m.name);
    if (k) return k;
    if (seen.has(m.name)) return "cycle";
    seen.add(m.name);
    const deps = m.imports.map((i) => `${i}=${byName.has(i) ? key(byName.get(i)!, seen) : "-"}`).sort();
    const out = sha256([fingerprint, m.name, m.text, ...deps].join("\0"));
    keys.set(m.name, out);
    return out;
  };
  for (const m of mods) key(m, new Set());
  return keys;
}

/**
 * vreact's record of the build directory it left behind (kept outside the project, next to the
 * library's own build): the hash of every file under `<out>/.lake` (and of `lake-manifest.json`),
 * the modules whose build log was current, and the modules the kernel re-check certified, each
 * with its key.
 */
interface BuildRecord {
  files: Record<string, string>;
  current: Record<string, string>;
  certified: Record<string, string>;
}

const recordPath = (leanLib: string, outDir: string) => path.join(leanLib, ".lake", "vreact-builds", sha256(fs.realpathSync(outDir)).slice(0, 40) + ".json");

/** The hashes of the files Lake keeps in the project: its build directory and its manifest (null: something there is not a plain file). */
function buildFiles(outDir: string): Record<string, string> | null {
  const out: Record<string, string> = {};
  const lake = path.join(outDir, ".lake");
  if (fs.existsSync(lake) || isLink(lake)) {
    if (!fs.lstatSync(lake).isDirectory()) return null;
    const files = treeFiles(lake);
    if (!files) return null;
    for (const f of files) out[path.join(".lake", f).split(path.sep).join("/")] = sha256(fs.readFileSync(path.join(lake, f)));
  }
  const manifest = path.join(outDir, "lake-manifest.json");
  if (isLink(manifest)) return null;
  if (fs.existsSync(manifest)) out["lake-manifest.json"] = sha256(fs.readFileSync(manifest));
  return out;
}

function isLink(p: string): boolean {
  try {
    return fs.lstatSync(p).isSymbolicLink();
  } catch {
    return false;
  }
}

function readRecord(p: string): BuildRecord | null {
  try {
    const r = JSON.parse(fs.readFileSync(p, "utf8")) as BuildRecord;
    return r && typeof r.files === "object" && typeof r.current === "object" && typeof r.certified === "object" ? r : null;
  } catch {
    return null;
  }
}

function writeRecord(p: string, r: BuildRecord) {
  fs.mkdirSync(path.dirname(p), { recursive: true });
  const tmp = `${p}.${process.pid}.tmp`;
  fs.writeFileSync(tmp, JSON.stringify(r));
  fs.renameSync(tmp, p);
}

const sameFiles = (a: Record<string, string>, b: Record<string, string>) => {
  const ka = Object.keys(a);
  return ka.length === Object.keys(b).length && ka.every((k) => b[k] === a[k]);
};

/** Lake's outputs of a module (`.olean`, `.ilean`, `.trace`, hashes, `.c`, …). */
function removeOutputs(outDir: string, mod: string) {
  const parts = mod.split(".");
  const last = parts[parts.length - 1];
  for (const base of [path.join(outDir, ".lake", "build", "lib", "lean"), path.join(outDir, ".lake", "build", "ir")]) {
    const dir = path.join(base, ...parts.slice(0, -1));
    if (!fs.existsSync(dir)) continue;
    for (const f of fs.readdirSync(dir)) if (f.startsWith(last + ".")) fs.rmSync(path.join(dir, f), { force: true });
  }
}

const oleanOf = (outDir: string, mod: string) => path.join(outDir, ".lake", "build", "lib", "lean", ...mod.split(".")) + ".olean";
const traceOf = (outDir: string, mod: string) => path.join(outDir, ".lake", "build", "lib", "lean", ...mod.split(".")) + ".trace";

/** A message as lake logs it (`<file>:<line>:<col>: <text>`) with its level, for module `rel`. */
function logEntryMessage(level: string, message: string, rel: string): LeanMessage | null {
  const severity = level === "error" ? "error" : level === "warning" ? "warning" : level === "info" ? "info" : null;
  if (!severity) return null;
  const m = /^(.+?\.lean):(\d+):(\d+): ?([\s\S]*)$/.exec(message);
  // a message of Lean has the position of the module's own file; anything else (lake's
  // `stdout:`/`stderr:` captures of the process) is no evidence, but an error stays an error
  if (!m || m[1].split("\\").join("/") !== rel) return severity === "info" ? null : { severity, file: rel, line: 0, col: 0, text: message };
  return { severity, file: rel, line: +m[2], col: +m[3], text: m[4] };
}

/** The messages of a module's own Lean run, from the build log lake stored with it. */
function traceMessages(outDir: string, mod: ProjectModule): LeanMessage[] {
  let log: { level?: string; message?: string }[] = [];
  try {
    const t = JSON.parse(fs.readFileSync(traceOf(outDir, mod.name), "utf8")) as { log?: unknown };
    if (Array.isArray(t.log)) log = t.log as typeof log;
  } catch {
    return [{ severity: "error", file: mod.rel, line: 0, col: 0, text: `the build log of ${mod.name} could not be read` }];
  }
  return log.flatMap((e) => {
    const m = typeof e?.message === "string" && typeof e?.level === "string" ? logEntryMessage(e.level, e.message, mod.rel) : null;
    return m ? [m] : [];
  });
}

/** Elaborate a module once more with `lean --json` (one whose build failed: lake keeps no log of it), for its structured messages. */
function rerunMessages(outDir: string, mod: ProjectModule, env: NodeJS.ProcessEnv): LeanMessage[] {
  const r = spawnSync("lake", ["env", "lean", "--json", mod.rel], { cwd: outDir, env, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
  if (r.error) throw new Error(`could not run lean: ${r.error.message}`);
  const out: LeanMessage[] = [];
  for (const line of (r.stdout ?? "").split("\n")) {
    if (!line.trim()) continue;
    let j: { severity?: string; pos?: { line?: number; column?: number }; data?: string; caption?: string; isSilent?: boolean } | null = null;
    try {
      j = JSON.parse(line);
    } catch {
      j = null;
    }
    if (!j || typeof j.data !== "string" || !j.pos) {
      out.push({ severity: "error", file: mod.rel, line: 0, col: 0, text: `lean printed: ${line.slice(0, 300)}` });
      continue;
    }
    if (j.isSilent) continue;
    const severity = j.severity === "error" ? "error" : j.severity === "warning" ? "warning" : "info";
    const text = j.caption?.trim() ? `${j.caption.trim()}:\n${j.data.trim()}` : j.data.trim();
    out.push({ severity, file: mod.rel, line: j.pos.line ?? 0, col: j.pos.column ?? 0, text });
  }
  if (r.status !== 0 && !out.some((m) => m.severity === "error")) out.push({ severity: "error", file: mod.rel, line: 0, col: 0, text: `lean exited with code ${r.status}${r.signal ? ` (${r.signal})` : ""}: ${(r.stderr ?? "").trim().split("\n").slice(-6).join("\n")}` });
  return out;
}

/** Modules lake reports as failed: `✖ [i/n] Building M` and the closing list of failed targets. */
function failedModules(raw: string): Set<string> {
  const out = new Set<string>();
  let list = false;
  for (const line of raw.split("\n")) {
    const j = /^✖ \[\d+\/\d+\] \S+ (\S+)/.exec(line);
    if (j) out.add(plainModule(j[1]));
    if (/^Some required targets logged failures:/.test(line)) list = true;
    else if (list && /^- \S+/.test(line)) out.add(plainModule(line.slice(2).trim()));
    else list = false;
  }
  return out;
}

/** The result of the kernel re-check (`lean/Certify.lean`). */
interface Certificate {
  certified: string[];
  failed: { module: string; reason: string }[];
  issues: { module: string; decl: string; msg: string }[];
}

/** Run `vreact-certify` on the built modules `check` (in import order), with `base` imported as they are. */
function runCertify(outDir: string, leanLib: string, env: NodeJS.ProcessEnv, base: string[], check: string[]): Certificate {
  const exe = path.join(leanLib, ".lake", "build", "bin", "vreact-certify");
  const r = spawnSync("lake", ["env", exe], { cwd: outDir, env, input: JSON.stringify({ base, check }), encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
  if (r.error) throw new Error(`could not run the kernel re-check ${exe}: ${r.error.message}`);
  let out: Certificate | null = null;
  try {
    const p = JSON.parse(r.stdout ?? "") as Certificate;
    if (Array.isArray(p?.certified) && Array.isArray(p?.failed) && Array.isArray(p?.issues)) out = p;
  } catch {
    out = null;
  }
  // never "certified" by a check that did not run to the end
  if (r.status !== 0 || !out) {
    return { certified: [], failed: check.map((module) => ({ module, reason: "the kernel re-check did not run to the end" })), issues: [{ module: "", decl: "", msg: `the kernel re-check failed (exit ${r.status}${r.signal ? `, ${r.signal}` : ""}): ${((r.stdout ?? "") + (r.stderr ?? "")).trim().split("\n").slice(-8).join("\n")}` }] };
  }
  return out;
}

/** The line of declaration `decl` in a Lean file (private names without their `_private.<module>.0.` prefix), 1 if not found. */
function declLine(outDir: string, rel: string, decl: string): number {
  if (!decl) return 1;
  const plain = decl.replace(/^_private\.(?:[^.]+\.)*?0\./, "");
  try {
    const d = leanDecls(fs.readFileSync(path.join(outDir, rel), "utf8"), rel).find((x) => x.name === plain || (x.name !== null && plain.startsWith(x.name + ".")));
    return d?.start ?? 1;
  } catch {
    return 1;
  }
}

/** The result of `runLake`. */
export interface LakeRun {
  /** Lean's messages about the project's modules (from their own Lean runs) and lake's own errors */
  messages: LeanMessage[];
  /** the same messages as lake-style text (`lakeMessages` reads it back; the regression suite doctors it) */
  raw: string;
  status: number;
  /** what lake printed */
  lakeOutput: string;
}

/**
 * Build the generated project with lake and collect Lean's messages about it.
 *
 * The report counts only evidence from Lean runs that vreact itself started on this machine:
 *  - the build directory (`<out>/.lake`, with every module's `.olean` and the build log lake
 *    replays for a module that is up to date) must be exactly the one vreact's last build left
 *    behind (`BuildRecord`, kept next to the library's build, outside the project): otherwise —
 *    a project copied with its `.vreact/`, a shared cache, an edited log — it is removed and
 *    everything is built again. Lake's shared artifact cache is off (`enableArtifactCache`).
 *  - before the build, the outputs of every module whose inputs changed since that build are
 *    removed, so afterwards a module has a build log (`.trace`) and an `.olean` exactly when its
 *    log comes from a Lean run on its current inputs (in this build, or an earlier one lake
 *    replays): its messages are read from that log, entry by entry — never from lake's printed
 *    text, where a message's lines cannot be told from another module's messages.
 *  - a module whose build failed (lake keeps no log of it) is elaborated once more with
 *    `lean --json` for its messages; a module that was not built has none (its obligations are
 *    not checked).
 *  - the built modules are re-checked by Lean's kernel in a fresh process (`vreact-certify`,
 *    `lean/Certify.lean`), and the user proofs inspected for what they added; a rejection is an
 *    error at the declaration, and every module importing a module that failed is broken.
 * Lake's printed text is used only for lake's own errors (which can only take away).
 */
export function runLake(outDir: string, leanLib: string): LakeRun {
  const env = buildLeanLib(leanLib);
  const mods = projectModules(outDir, leanLib);
  const byName = new Map(mods.map((m) => [m.name, m]));
  const keys = moduleKeys(mods, libraryFingerprint(leanLib, outDir));
  const recPath = recordPath(leanLib, outDir);
  let rec = readRecord(recPath);
  const before = buildFiles(outDir);
  if (!rec || !before || !sameFiles(rec.files, before)) {
    fs.rmSync(path.join(outDir, ".lake"), { recursive: true, force: true });
    fs.rmSync(path.join(outDir, "lake-manifest.json"), { force: true });
    rec = null;
  }
  for (const m of mods) if (rec?.current[m.name] !== keys.get(m.name)) removeOutputs(outDir, m.name);
  const r = spawnSync("lake", ["build"], { cwd: outDir, env, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
  if (r.error) throw new Error(`could not run lake (is Lean installed? see SKILL.md): ${r.error.message}`);
  const lakeOutput = (r.stdout ?? "") + (r.stderr ?? "");
  const status = r.status ?? 1;
  const current = new Set(mods.filter((m) => fs.existsSync(oleanOf(outDir, m.name)) && fs.existsSync(traceOf(outDir, m.name))).map((m) => m.name));
  const failed = failedModules(lakeOutput);
  // messages, module by module
  const perModule: { mod: ProjectModule; ok: boolean; messages: LeanMessage[] }[] = [];
  for (const m of mods) {
    if (current.has(m.name)) perModule.push({ mod: m, ok: true, messages: traceMessages(outDir, m) });
    else if (failed.has(m.name) && m.imports.every((i) => !byName.has(i) || current.has(i))) perModule.push({ mod: m, ok: false, messages: rerunMessages(outDir, m, env) });
  }
  // lake's own errors (no position in a module: imports, cycles, the lakefile, crashes)
  const lakeErrors = parseMessages(lakeOutput).filter((x) => x.severity === "error" && (!x.line || !x.file || !byName.has(modOfRel(x.file))));
  // the kernel re-check of the modules built from current inputs
  const certified = new Set(mods.filter((m) => current.has(m.name) && rec?.certified[m.name] === keys.get(m.name)).map((m) => m.name));
  const order: string[] = [];
  const visit = (n: string, seen: Set<string>) => {
    if (seen.has(n) || !current.has(n) || certified.has(n)) return;
    seen.add(n);
    for (const i of byName.get(n)!.imports) if (byName.has(i)) visit(i, seen);
    order.push(n);
  };
  const seen = new Set<string>();
  for (const m of mods) visit(m.name, seen);
  const certMessages: LeanMessage[] = [];
  /** modules the re-check failed, with the reason */
  const uncertified = new Map<string, string>();
  if (order.length) {
    const cert = runCertify(outDir, leanLib, env, [...certified], order);
    for (const c of cert.certified) certified.add(c);
    for (const i of cert.issues) {
      const rel = i.module ? relOfMod(i.module) : "";
      certMessages.push({ severity: "error", file: rel, line: rel ? declLine(outDir, rel, i.decl) : 0, col: 0, text: `${i.module ? `${i.module}${i.decl ? ` (${i.decl})` : ""}: ` : ""}${i.msg}` });
    }
    for (const f of cert.failed) uncertified.set(f.module, f.reason);
  }
  // A generated module elaborated but not certified is broken as a whole: one the re-check
  // failed (its replay stops at the first declaration the kernel rejects, and a module importing
  // a failed one is not checked), and one whose build failed (no `.olean`: never certified, its
  // messages from `lean --json`) that imports a module the re-check failed.
  for (const p of perModule) {
    const m = p.mod.name;
    if (!m.startsWith("VTS.")) continue;
    let why = uncertified.get(m);
    if (why === undefined && !p.ok) {
      const up = p.mod.imports.find((i) => uncertified.has(i));
      if (up !== undefined) why = `it imports ${up}, which failed the check: ${uncertified.get(up)!.replace(/^it imports \S+, which failed the check: /, "")}`;
    }
    if (why === undefined) continue;
    const line = p.mod.text.split("\n").findIndex((l) => /^import /.test(l)) + 1 || 1;
    certMessages.push({ severity: "error", file: p.mod.rel, line, col: 0, text: `the kernel re-check did not certify ${m}: ${why}`, wholeFile: true });
  }
  const messages = [...perModule.flatMap((p) => p.messages), ...lakeErrors, ...certMessages];
  if (status !== 0 && !messages.some((m) => m.severity === "error")) {
    const tail = lakeOutput.trim().split("\n").slice(-12).join("\n");
    messages.push({ severity: "error", file: "", line: 0, col: 0, text: `lake build failed (exit ${status}${r.signal ? `, ${r.signal}` : ""})${tail ? ":\n" + tail : ""}` });
  }
  // the record of this build directory, for the next build
  const after = buildFiles(outDir);
  if (after) {
    const cur: Record<string, string> = {};
    const cer: Record<string, string> = {};
    for (const m of mods) {
      if (current.has(m.name)) cur[m.name] = keys.get(m.name)!;
      if (certified.has(m.name)) cer[m.name] = keys.get(m.name)!;
    }
    writeRecord(recPath, { files: after, current: cur, certified: cer });
  } else fs.rmSync(recPath, { force: true });
  // the same messages as lake-style text
  const lines: string[] = [];
  perModule.forEach((p, i) => {
    lines.push(`${p.ok ? "✔" : "✖"} [${i + 1}/${perModule.length}] ${p.ok ? "Built" : "Building"} ${p.mod.name}`);
    for (const x of p.messages) lines.push(`${x.severity}: ${x.file}${x.line ? `:${x.line}:${x.col}` : ""}: ${x.text}`);
  });
  for (const x of [...lakeErrors, ...certMessages]) lines.push(`error: ${x.file ? `${x.file}${x.line ? `:${x.line}:${x.col}` : ""}: ` : ""}${x.text}`);
  lines.push(status === 0 ? "Build completed successfully." : "error: build failed");
  return { messages, raw: lines.join("\n") + "\n", status, lakeOutput };
}

/** Lean's messages in lake's output; a failed build is never read as "nothing to report". */
export function lakeMessages(raw: string, status: number, signal?: string | null): LeanMessage[] {
  const messages = parseMessages(raw);
  if (status !== 0 && !messages.some((m) => m.severity === "error")) {
    const tail = raw.trim().split("\n").slice(-12).join("\n");
    messages.push({ severity: "error", file: "", line: 0, col: 0, text: `lake build failed (exit ${status}${signal ? `, ${signal}` : ""})${tail ? ":\n" + tail : ""}` });
  }
  return messages;
}

const HEAD = /^(error|warning|info): (.+?\.lean):(\d+):(\d+): ?(.*)$/;
/** Lake/Lean errors without a position: bad import, build cycle, missing file, lakefile, … */
const HEAD_NOPOS = /^error: (?:(.+?\.lean): )?(.*)$/;
/** Crashes of the Lean process itself. */
const PANIC = /^(PANIC|INTERNAL PANIC|uncaught exception|libc\+\+abi|Stack overflow|Segmentation fault)\b/;
const STOP = /^(error|warning|info|trace|✖|⚠|✔|ℹ|Some required targets|Build completed|- )/;
/** The line with which lake starts the log of a job: `✔ [4/9] Built VTS.m.Defs (1.2s)`, `ℹ [5/9] Replayed …`, `✖ [6/9] Building Proofs.m`. */
const JOB = /^[✔✖⚠ℹ] \[\d+\/\d+\] \S+ (\S+)/;
/** Lake's closing summary (after the last job's log). */
const SUMMARY = /^(Some required targets logged failures:|Build completed|error: build failed)/;

/** Whether `file` (as Lean names it: relative to the project, or absolute) is module `mod`'s source, `VTS/m/Defs.lean` for `VTS.m.Defs`. */
const isFileOf = (file: string, mod: string) => {
  const f = file.split("\\").join("/");
  const own = mod.split(".").join("/") + ".lean";
  return f === own || f === "./" + own || (f.startsWith("/") && f.endsWith("/" + own));
};
/** The module a job name names (`VTS.m.Defs`, also as `vts/+VTS.m.Defs:leanArts`), without Lean's `«…»` escapes. */
const plainModule = (name: string) => name.replace(/^[^/\s]*\/\+?/, "").replace(/:[\w.]+$/, "").replace(/[«»]/g, "");

/**
 * Lean's messages in lake's output. Lake prints the log of each job (a module's elaboration)
 * after a line `✔ [i/n] Built M` (`Replayed`, `✖ … Building`, …), a message per line `info:
 * <file>:<line>:<col>: <text>` with any further lines of its text as they are. So a message's
 * text could contain a line that reads like a message of another file (a user proof printing
 * "…\ninfo: VTS/m/Posts.lean:14:16: vreact:ok"). The positive evidence the report counts — infos
 * (`vreact:ok`, the sentinel, axiom reports) — is therefore taken only from the log of the job of
 * the module whose file it names: an info line naming another file belongs to the text of the
 * message before it. (Errors and warnings are taken wherever they appear: they can only take
 * away from the verdict. User proofs may not contain line breaks in literals or names at all,
 * `ProofCheck.lean`.)
 */
export function parseMessages(raw: string): LeanMessage[] {
  const out: LeanMessage[] = [];
  let cur: LeanMessage | null = null;
  let generic: LeanMessage | null = null;
  /** the module whose job log the current line is in (null: outside any job's log) */
  let job: string | null = null;
  for (const line of raw.split("\n")) {
    const j = JOB.exec(line);
    if (j) {
      if (cur) out.push(cur);
      cur = null;
      job = plainModule(j[1]);
      continue;
    }
    if (SUMMARY.test(line)) job = null;
    const m = HEAD.exec(line);
    if (m && (m[1] !== "info" || (job !== null && isFileOf(m[2], job)))) {
      if (cur) out.push(cur);
      cur = { severity: m[1] as LeanMessage["severity"], file: m[2], line: +m[3], col: +m[4], text: m[5] };
      continue;
    }
    if (m) {
      // an info line in another module's log (or outside any): text of the message before it
      if (cur) cur.text += "\n" + line;
      continue;
    }
    const n = HEAD_NOPOS.exec(line) ?? (PANIC.test(line) ? [line, undefined, line] : null);
    if (n) {
      if (cur) out.push(cur);
      cur = null;
      const msg: LeanMessage = { severity: "error", file: n[1] ?? "", line: 0, col: 0, text: n[2] };
      // the closing summary only matters when lake gave no other reason
      if (n[1] === undefined && /^build failed$/.test(n[2])) generic = msg;
      else cur = msg;
      continue;
    }
    if (cur && STOP.test(line)) {
      out.push(cur);
      cur = null;
      continue;
    }
    if (cur) cur.text += "\n" + line;
  }
  if (cur) out.push(cur);
  if (generic && !out.some((m) => m.severity === "error")) out.push(generic);
  return out;
}

/** Generated files (as opposed to user proofs, copied to `Proofs/`) live under `VTS/`. */
export const isGenerated = (rel: string) => /^VTS(?:\/|\\|\.lean$)/.test(rel);

/** Locate the `/-⟦obN⟧-/` markers in the generated files (never in user proofs: an error there is never an obligation's). */
export function findMarkers(outDir: string): Marker[] {
  const markers: Marker[] = [];
  const walk = (d: string) => {
    if (!fs.existsSync(d)) return;
    for (const f of fs.readdirSync(d)) {
      const p = path.join(d, f);
      if (fs.statSync(p).isDirectory()) {
        if (f !== ".lake") walk(p);
      } else if (f.endsWith(".lean")) {
        const lines = fs.readFileSync(p, "utf8").split("\n");
        lines.forEach((l, i) => {
          // `/-⟦gen⟧-/` (id 0) marks a generated proof that is not a user obligation
          const re = /\/-⟦(?:ob(\d+)|gen)⟧-\//g;
          let mm;
          while ((mm = re.exec(l))) markers.push({ id: mm[1] ? +mm[1] : 0, file: path.relative(outDir, p), line: i + 1, col: [...l.slice(0, mm.index)].length });
        });
      }
    }
  };
  walk(path.join(outDir, "VTS"));
  return markers;
}

/** A top-level command of a generated Lean file (lines `start..end`, 1-based, inclusive). */
export interface LeanDecl {
  file: string;
  start: number;
  end: number;
  /** fully qualified name of the declaration; null for other commands (#print, namespace, …) */
  name: string | null;
  kind: string;
}

// A keyword opens a command only when followed by white space or the end of the line: a
// translated VTS name that is a Lean keyword carries a `'` (`end'`, `open'`, `def'`), and such
// a name may begin a continuation line of a term at column 0 (`end')`).
const DECL_KW = /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|axiom|structure|inductive|instance|example|opaque|class)(?=\s|$)\s*([^\s:({[⦃]*)/;
const CMD_KW = /^(\/--|@\[|#[a-z_]+(?=\s|$)|(?:namespace|end|section|noncomputable section|open|set_option|import|attribute|deriving instance|macro_rules|macro|syntax|elab|grind_pattern|universe|variable|mutual)(?=\s|$))/;

/**
 * Split generated Lean text into its top-level commands. The generator writes every
 * command at column 0 (continuation lines of a term may also start at column 0, so only
 * known command keywords open a new span); a doc comment or attribute line belongs to the
 * declaration that follows it.
 */
export function leanDecls(text: string, file = ""): LeanDecl[] {
  const lines = text.split("\n");
  const out: LeanDecl[] = [];
  const stack: string[][] = [];
  let pending: LeanDecl | null = null; // a `/-- … -/` or `@[…]` line waiting for its declaration
  const qualify = (n: string) => (n.startsWith("_root_.") ? n.slice(7) : [...stack.flat(), n].join("."));
  lines.forEach((l, i) => {
    const ln = i + 1;
    const d = DECL_KW.exec(l);
    if (d) {
      const name = d[2] ? qualify(d[2]) : null;
      if (pending) Object.assign(pending, { name, kind: d[1] });
      else out.push({ file, start: ln, end: ln, name, kind: d[1] });
      pending = null;
      return;
    }
    const c = CMD_KW.exec(l);
    if (!c) return;
    if (pending && (c[1] === "/--" || c[1] === "@[")) return; // more modifiers of the same declaration
    pending = null;
    const span: LeanDecl = { file, start: ln, end: ln, name: null, kind: c[1] };
    out.push(span);
    if (c[1] === "/--" || c[1] === "@[") pending = span;
    else if (c[1] === "namespace") stack.push(l.slice(10).trim().split("."));
    else if (c[1] === "section" || c[1] === "noncomputable section") stack.push([]);
    else if (c[1] === "end") stack.pop();
  });
  out.forEach((d, k) => (d.end = k + 1 < out.length ? out[k + 1].start - 1 : lines.length));
  return out;
}

/** The command of `decls` (sorted by line) that contains `line`. */
export function declAt(decls: LeanDecl[] | undefined, line: number): LeanDecl | undefined {
  if (!decls) return undefined;
  for (const d of decls) if (d.start <= line && line <= d.end) return d;
  return undefined;
}

/** Top-level commands of every generated and user-proof file, by path relative to `outDir`. */
export function findDecls(outDir: string): Map<string, LeanDecl[]> {
  const out = new Map<string, LeanDecl[]>();
  const walk = (d: string) => {
    if (!fs.existsSync(d)) return;
    for (const f of fs.readdirSync(d)) {
      const p = path.join(d, f);
      if (fs.statSync(p).isDirectory()) {
        if (f !== ".lake") walk(p);
      } else if (f.endsWith(".lean")) {
        const rel = path.relative(outDir, p);
        out.set(rel, leanDecls(fs.readFileSync(p, "utf8"), rel));
      }
    }
  };
  walk(outDir);
  return out;
}

/** A runtime limit hit outside `vreact_ob` (which reports its own as a failure warning): the declaration was aborted. */
const ABORT = /\(deterministic\) timeout|maximum recursion depth has been reached/;
const isAbort = (text: string) => ABORT.test(text) && !text.startsWith("vreact:");
const BUILD = /bad import|unknown module prefix|build cycle|no such file|does not exist|import .* failed|environment already contains|object file|lakefile|unknown package|failed to (?:load|read|fetch)/;
const FOLLOW_ON = /Unknown (?:identifier|constant)|unknown (?:identifier|constant)/;
/** The sentinel `#eval "vreact:checked"` that ends every generated file: Lean got to the end of it. */
const SENTINEL = /^"vreact:checked"$/;
/**
 * `vreact_ob`'s result at an obligation's marker: proved (info), failed (a warning; the goal
 * was admitted), or blocked (a warning: it depends on `sorry` from elsewhere that its goal
 * or the proof found contains, so it was not checked on its own; the goal was admitted)
 */
const OB_OK = /^vreact:ok$/;
const OB_FAIL = /^vreact: /;
const OB_BLOCKED = /^vreact:blocked /;

export interface Verdict {
  proved: Obligation[];
  failed: { ob: Obligation; message: string }[];
  /** obligations whose proof was not (or not completely) checked; see `reasons` */
  unchecked: Obligation[];
  /** errors not attributable to a single obligation (each with its `cause`) */
  internal: LeanMessage[];
  axioms: Map<string, string[]>;
  /**
   * `#vreact_assumed X`: the declarations outside the generated code (user proofs) in `X`'s
   * cone that use `VReact.assumed` directly (empty: every use is an `assume(…)` of the
   * program); missing when Lean printed no such report for `X`
   */
  assumedOutside: Map<string, string[]>;
  /** why an obligation in `unchecked` was not established */
  reasons: Map<number, string>;
  /** generated declarations that did not elaborate cleanly: name → first error */
  declErrors: Map<string, string>;
  /**
   * generated commands with an error that is not an obligation's (at no marker) or that a
   * runtime limit aborted: such a declaration may be missing from the environment, or another
   * declaration of that name (e.g. from a user proof) may stand in for it
   */
  brokenDecls: { name: string | null; kind: string; file: string; error: string }[];
  /** `declaration uses 'sorry'` warnings in generated files and user proofs */
  sorries: LeanMessage[];
  /** generated files Lean elaborated to the end */
  checkedFiles: Set<string>;
  /** obligations in `unchecked` that `vreact_ob` could not check: they depend on `sorry` from elsewhere (in their goal or the proof found) */
  blocked: Set<number>;
}

/** `#print axioms X` (the generator writes one per line) */
const PRINT_AXIOMS = /^#print axioms (\S+)\s*$/;
/** `#vreact_assumed X` (VReact/Assumed.lean; the generator writes one after each `#print axioms X`) */
const ASSUMED_AUDIT = /^#vreact_assumed (\S+)\s*$/;
const SENTINEL_CMD = '#eval "vreact:checked"';

/** Modules lake reports as built (✔ Built/Replayed) or attempted (✖ Building). */
export function builtModules(raw: string): Set<string> {
  const out = new Set<string>();
  for (const line of raw.split("\n")) {
    const m = /^[✔✖⚠] \[\d+\/\d+\] (?:Built|Building|Replayed|Checked) ([\w.«»']+)/.exec(line);
    if (m) out.add(m[1]);
  }
  return out;
}

/**
 * Attribute Lean's messages to obligations and declarations.
 *
 * `vreact_ob` (VReact/Budget.lean) reports every obligation it ran at its marker: the info
 * `vreact:ok` when the automation proved it, a warning `vreact: <why>` when it did not, and
 * a warning `vreact:blocked <why>` when it depends on `sorry` from elsewhere (its goal or the
 * proof found contains one: then the obligation is not checked rather than proved or
 * failed); in both cases the goal is
 * admitted with `sorry`, so the module still builds. An obligation counts as proved only if
 *  - every copy of its marker has that positive evidence and none has a failure (a
 *    `vreact:` warning or an error at the marker; a forged `vreact:ok` next to a failure does
 *    not help, and missing evidence means "not checked", never "proved");
 *  - its file was elaborated to the end (the `vreact:checked` sentinel was printed);
 *  - its declaration has no other error: an error elsewhere in the declaration (a timeout at
 *    the declaration start, an elaboration error, an aborting runtime limit) means Lean may
 *    not have kept the obligation's proof.
 * (The report also requires that the axioms of the obligation's item are reported, and that
 * `sorryAx` in them is explained by a reported failure or sorry; see `reportFrom`.)
 * Lake errors without a position are kept as `build` errors. Evidence, axiom reports and the
 * sentinel count only when Lean printed them at the generator's marker / `#print axioms X` /
 * `#vreact_assumed X` / sentinel position in a generated file, as infos `parseMessages` took
 * from the job log of that generated module: a user proof printing the same text prints it at
 * its own position, and a line of its message that reads like a generated file's message is
 * text of that message (proof files may not contain line breaks in literals and names either:
 * `ProofCheck.lean`); a result at the marker of no known obligation is not an obligation's.
 */
export function judge(obligations: Obligation[], messages: LeanMessage[], markers: Marker[], outDir: string, _built?: Set<string>): Verdict {
  const decls = findDecls(outDir);
  const failedIds = new Map<number, string>();
  /** the marker copies with positive evidence */
  const okMarkers = new Set<Marker>();
  /** obligations `vreact_ob` could not check (they depend on `sorry` from elsewhere) */
  const blockedIds = new Map<number, string>();
  /** declarations with a failed or blocked obligation copy (their `sorry` is the admitted goal) */
  const failedDecls = new Set<LeanDecl>();
  const internal: LeanMessage[] = [];
  const axioms = new Map<string, string[]>();
  const assumedOutside = new Map<string, string[]>();
  const checkedFiles = new Set<string>();
  const sorries: LeanMessage[] = [];
  const declErrors = new Map<string, string>();
  /** per declaration: unattributed errors, and whether a runtime limit aborted it */
  const bad = new Map<LeanDecl, { errs: LeanMessage[]; aborted: boolean; failedObs: number }>();
  const badOf = (d: LeanDecl) => bad.get(d) ?? (bad.set(d, { errs: [], aborted: false, failedObs: 0 }), bad.get(d)!);
  const generated = (rel: string) => decls.has(rel);
  const known = new Set(obligations.map((ob) => ob.id));
  const firstErr = new Map<string, LeanMessage>();
  const markersAt = new Map<string, Marker[]>();
  for (const mk of markers) markersAt.set(`${mk.file}:${mk.line}`, [...(markersAt.get(`${mk.file}:${mk.line}`) ?? []), mk]);
  /** the marker of a known obligation on the message's line closest to the left of its column */
  const markerOf = (rel: string, msg: LeanMessage): Marker | null => {
    if (!msg.line || !isGenerated(rel)) return null;
    const cands = (markersAt.get(`${rel}:${msg.line}`) ?? []).filter((mk) => mk.col <= msg.col && msg.col <= mk.col + 40);
    const mk = cands.length ? cands.reduce((a, b) => (b.col > a.col ? b : a)) : null;
    // (a marker of no known obligation cannot take a result: an error there stays the declaration's)
    return mk && mk.id !== 0 && known.has(mk.id) ? mk : null;
  };
  // the lines of the generated files: an axiom report or the sentinel counts only when Lean
  // printed it for the command the generator wrote at that line (never from a user proof)
  const texts = new Map<string, string[]>();
  const linesOf = (rel: string) => {
    if (!isGenerated(rel) || !decls.has(rel)) return undefined;
    if (!texts.has(rel)) texts.set(rel, fs.readFileSync(path.join(outDir, rel), "utf8").split("\n"));
    return texts.get(rel)!;
  };
  const failAt = (mk: Marker, d: LeanDecl | undefined, text: string) => {
    if (!failedIds.has(mk.id)) failedIds.set(mk.id, text);
    if (d) failedDecls.add(d), badOf(d).failedObs++;
  };
  for (const msg of messages) {
    const rel = msg.file ? path.normalize(path.isAbsolute(msg.file) ? path.relative(outDir, msg.file) : msg.file) : msg.file;
    msg.file = rel;
    const d = msg.line ? declAt(decls.get(rel), msg.line) : undefined;
    msg.decl = d?.name ?? null;
    if (msg.severity === "info") {
      if (OB_OK.test(msg.text.trim())) {
        const mk = markerOf(rel, msg);
        if (mk) okMarkers.add(mk);
        continue;
      }
      const lines = msg.line ? linesOf(rel) : undefined;
      const cmd = lines?.[msg.line - 1]?.trim();
      const pa = cmd ? PRINT_AXIOMS.exec(cmd) : null;
      if (pa) {
        // keyed by the name the generator wrote (Lean names may themselves contain `'`);
        // several reports for one name are joined (a further report can only add axioms)
        const am = /^'(.+?)' depends on axioms: \[([^\]]*)\]/.exec(msg.text);
        const got = am ? am[2].split(",").map((s) => s.trim()).filter(Boolean) : /^'(.+?)' does not depend on any axioms/.test(msg.text) ? [] : null;
        if (got) axioms.set(pa[1], [...new Set([...(axioms.get(pa[1]) ?? []), ...got])]);
      }
      const aa = cmd ? ASSUMED_AUDIT.exec(cmd) : null;
      if (aa) {
        // (likewise keyed by the generator's name and joined: a further report can only add)
        const am = /^'(.+?)' uses VReact\.assumed outside the generated code: \[([^\]]*)\]/.exec(msg.text);
        if (am) assumedOutside.set(aa[1], [...new Set([...(assumedOutside.get(aa[1]) ?? []), ...am[2].split(",").map((s) => s.trim()).filter(Boolean)])]);
      }
      if (cmd === SENTINEL_CMD && SENTINEL.test(msg.text.trim()) && lines!.slice(msg.line).every((l) => !l.trim())) checkedFiles.add(rel);
      continue;
    }
    if (msg.severity === "warning") {
      if (OB_FAIL.test(msg.text) || OB_BLOCKED.test(msg.text)) {
        // an obligation `vreact_ob` could not prove or not check (its goal was admitted with `sorry`)
        const mk = markerOf(rel, msg);
        if (mk && OB_BLOCKED.test(msg.text)) {
          if (!blockedIds.has(mk.id)) blockedIds.set(mk.id, msg.text.replace(OB_BLOCKED, ""));
          if (d) failedDecls.add(d);
          continue;
        }
        if (mk) {
          failAt(mk, d, msg.text.replace(OB_FAIL, ""));
          continue;
        }
        // in a generated file but at no obligation's marker (not where the generator put a
        // `vreact_ob`): a failure of the declaration it lies in
        if (isGenerated(rel) && generated(rel)) {
          if (d) badOf(d).errs.push(msg);
          internal.push(msg);
        }
        continue;
      }
      if (generated(rel) && /declaration uses [`']sorry[`']/.test(msg.text)) sorries.push(msg);
      continue;
    }
    if (msg.wholeFile) {
      // every declaration of the file is broken (its obligations are not counted; an error of
      // its own, processed before, stays its first), the error itself is not listed: its cause is
      for (const x of decls.get(rel) ?? []) {
        if (!x.name) continue;
        badOf(x).errs.push(msg);
        if (!declErrors.has(x.name)) declErrors.set(x.name, msg.text);
      }
      continue;
    }
    if (generated(rel) && msg.line && (firstErr.get(rel)?.line ?? Infinity) > msg.line) firstErr.set(rel, msg);
    if (d?.name && !declErrors.has(d.name)) declErrors.set(d.name, msg.text);
    const mk = markerOf(rel, msg);
    if (mk) {
      failAt(mk, d, msg.text);
      if (d && isAbort(msg.text)) badOf(d).aborted = true;
      continue;
    }
    if (d) badOf(d).errs.push(msg);
    internal.push(msg);
  }
  // classify the unattributed errors
  for (const msg of internal) {
    msg.cause ??=
      PANIC.test(msg.text) ? "internal"
      : !msg.file || !msg.line || (BUILD.test(msg.text) && !msg.decl) ? "build"
      : msg.file.startsWith("Proofs" + path.sep) || msg.file.startsWith("Proofs/") ? "proof"
      : isAbort(msg.text) ? "timeout"
      : FOLLOW_ON.test(msg.text) && (firstErr.get(msg.file)?.line ?? Infinity) < msg.line ? "follow-on"
      : "internal";
  }
  const brokenDecls: Verdict["brokenDecls"] = [];
  for (const [d, b] of bad) {
    if (!isGenerated(d.file) || !(b.errs.length || b.aborted)) continue;
    brokenDecls.push({ name: d.name, kind: d.kind, file: d.file, error: b.errs[0]?.text.split("\n")[0] ?? "a runtime limit aborted the declaration" });
  }
  const proved: Obligation[] = [];
  const failed: { ob: Obligation; message: string }[] = [];
  const unchecked: Obligation[] = [];
  const reasons = new Map<number, string>();
  // an obligation may have several copies (a precondition binder is repeated in the
  // postcondition theorems): it is proved only if every copy is
  const markersOf = new Map<number, Marker[]>();
  for (const mk of markers) markersOf.set(mk.id, [...(markersOf.get(mk.id) ?? []), mk]);
  const pending = new Map<LeanDecl, Obligation[]>();
  const blockedObs = new Set<number>();
  for (const ob of obligations) {
    const f = failedIds.get(ob.id);
    const mks = markersOf.get(ob.id) ?? [];
    if (f !== undefined) {
      failed.push({ ob, message: f });
      continue;
    }
    if (!mks.length) {
      unchecked.push(ob);
      reasons.set(ob.id, "its proof is missing from the generated Lean (translator bug)");
      internal.push({ severity: "error", file: "", line: 0, col: 0, text: `obligation ${ob.where} [${ob.kind}] is missing from the generated Lean`, cause: "internal" });
      continue;
    }
    const notChecked = mks.find((mk) => !checkedFiles.has(mk.file));
    if (notChecked) {
      unchecked.push(ob);
      const own = firstErr.get(notChecked.file);
      reasons.set(ob.id, own
        ? `Lean did not get to the end of ${notChecked.file}: it stopped after an error in it (line ${own.line}: ${own.text.split("\n")[0].slice(0, 100)})`
        : `${notChecked.file} was not checked: a module it imports failed, or the file stopped at an error in its imports`);
      continue;
    }
    const broken = mks.map((mk) => declAt(decls.get(mk.file), mk.line)).find((d) => {
      const b = d && bad.get(d);
      return !!b && (b.errs.length > 0 || b.aborted);
    });
    if (broken) {
      pending.set(broken, [...(pending.get(broken) ?? []), ob]);
      continue;
    }
    const blocked = blockedIds.get(ob.id);
    if (blocked !== undefined) {
      unchecked.push(ob);
      blockedObs.add(ob.id);
      reasons.set(ob.id, `it depends on \`sorry\` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()) that its goal or its proof contains, so Lean could not check it on its own: fix that first`);
      continue;
    }
    const silent = mks.find((mk) => !okMarkers.has(mk));
    if (silent) {
      unchecked.push(ob);
      reasons.set(ob.id, `Lean reported no result for it (no \`vreact:ok\` at ${silent.file}:${silent.line}:${silent.col}): its proof was not run, so it is not counted as proved`);
      continue;
    }
    proved.push(ob);
  }
  // obligations of declarations that failed for a reason Lean did not report at a marker
  for (const [d, obs] of pending) {
    const b = bad.get(d)!;
    // (an error of the declaration itself before the re-check's verdict on its whole file)
    const err = b.errs.find((e) => !e.wholeFile) ?? b.errs[0];
    const why = err ? err.text.split("\n")[0] : "a runtime limit aborted the declaration";
    const where = err ? `${err.file}:${err.line}:${err.col}` : d.file;
    const dn = d.name ?? `the declaration at ${d.file}:${d.start}`;
    if (err?.wholeFile)
      for (const ob of obs) {
        unchecked.push(ob);
        reasons.set(ob.id, `${why}, so this obligation is not counted as proved`);
      }
    else if (obs.length === 1 && b.failedObs === 0 && err) failed.push({ ob: obs[0], message: `error in the declaration of this obligation (${dn}) at ${where}:\n${err.text}` });
    else
      for (const ob of obs) {
        unchecked.push(ob);
        reasons.set(ob.id, `${dn} did not elaborate (${why}), so Lean may not have finished this obligation`);
      }
  }
  // the `sorry` warning of a declaration with a failed obligation is that obligation's
  // admitted goal (reported as the failure), not a hole
  const admitted = (s: LeanMessage) => {
    const d = s.line ? declAt(decls.get(s.file), s.line) : undefined;
    return !!d && failedDecls.has(d);
  };
  return { proved, failed, unchecked, internal, axioms, assumedOutside, reasons, declErrors, brokenDecls, sorries: sorries.filter((s) => !admitted(s)), checkedFiles, blocked: blockedObs };
}

/**
 * Keep the informative part of a Lean failure (the goal), in at most `maxLines` lines. A message
 * that fits is kept as it is (without `grind`'s diagnostics). A longer one is shortened step by
 * step, each step only while it is still too long:
 *   1. a message with several goals (after a timeout: the goal as stated, then the case of it
 *      that failed; several unsolved goals) keeps only the last goal, after the lines before the
 *      first one (what failed), so the hypotheses shown are always those of the conclusion shown;
 *   2. the contract instances that span several lines (`hcontract…`, the facts `vreact_contracts`
 *      adds for each call of a function with `ensures`) become one line that names and counts
 *      them, where the first of them was;
 *   3. then the let-definitions that span several lines (`x : T :=` and its value, code that the
 *      source shows), from the top and only as many as needed, likewise one line;
 *   4. then the other hypotheses that span several lines, from the top and only as many as
 *      needed, likewise (not the hypothesis right above the conclusion);
 *   5. last, the conclusion (the last `⊢ …`) is cut to 3 lines and what follows it to 2; from the
 *      conclusion up, each hypothesis is shown whole while it fits, a long one that does not fit
 *      as one line that names it, and the hypotheses farthest from the conclusion are left out,
 *      named and counted by one line `… (k earlier hypotheses: …)` (the lines of steps 2-4 stay).
 * So the hypotheses next to the conclusion (usually the ones that decide the case: branch
 * conditions, the negated goal; the one right above the conclusion whole whenever it fits) and
 * the conclusion stay in view, and every line that stands for others says so (`--full shows
 * …`). `--full` prints the message unchanged.
 */
export function summarizeLeanError(text: string, maxLines = 30): string {
  const lines = text.split("\n");
  const cut = lines.findIndex((l) => /\[grind\] Goal diagnostics|\[grind\] Diagnostics/.test(l));
  const kept = (cut > 0 ? lines.slice(0, cut) : lines).filter((l) => l.trim() !== "");
  if (kept.length <= maxLines) return kept.join("\n");
  // blocks: a line at column 0 and the indented lines that continue it (a hypothesis `h : …`
  // whose type Lean broke over several lines, the conclusion `⊢ …`)
  let blocks: string[][] = [];
  for (const l of kept) {
    if (/^\s/.test(l) && blocks.length) blocks[blocks.length - 1].push(l);
    else blocks.push([l]);
  }
  // (the lines that stand for others, with the names they stand for)
  const notes = new Map<string[], string[]>();
  const names = (b: string[]) => notes.get(b) ?? /^((?:[^\s:]+ )*[^\s:]+) :(?: |$)/.exec(b[0])?.[1].split(" ") ?? [];
  const isTarget = (b: string[]) => b[0].startsWith("⊢");
  // 1. several goals: the last one only (cut anywhere else, the hypotheses of one goal would
  // stand above the conclusion of another: after a timeout, the goal as stated above the failing
  // case's)
  const targets = blocks.flatMap((b, i) => (isTarget(b) ? [i] : []));
  if (targets.length >= 2) {
    const prev = targets[targets.length - 2];
    const start = blocks.findIndex((b) => isTarget(b) || names(b).length > 0 || /^case /.test(b[0]));
    const rest = blocks.slice(prev + 1);
    const what = /^The goal splits into \d+ cases/.test(rest[0][0]) ? "the goal as stated" : targets.length === 2 ? "an earlier goal" : `${targets.length - 1} earlier goals`;
    blocks = [...blocks.slice(0, start), [`  … (${what}: --full shows ${targets.length === 2 ? "it" : "them"})`], ...rest];
  }
  const size = (bs: string[][]) => bs.reduce((k, b) => k + b.length, 0);
  // the lines before the first hypothesis (what failed, the case's name), the hypotheses, and
  // the conclusion with what follows it
  const ti = blocks.map(isTarget).lastIndexOf(true);
  const end = ti < 0 ? blocks.length : ti;
  let h0 = blocks.findIndex((b) => names(b).length > 0 || isTarget(b));
  if (h0 < 0 || h0 > end) h0 = end;
  const head = blocks.slice(0, h0);
  let hyps = blocks.slice(h0, end);
  const rest = blocks.slice(end);
  const a = (k: number, one: string, many: string) => (k === 1 ? `${/^[aeiou]/.test(one) ? "an" : "a"} ${one}` : `${k} ${many}`);
  /** `base` with the blocks `picked` as one line that names and counts them, where the first was */
  const collapsed = (base: string[][], picked: string[][], sep: string, one: string, many: string): string[][] => {
    if (!picked.length) return base;
    const all = picked.flatMap(names);
    const line = [`${all.join(", ")} ${sep} …  (${a(all.length, one, many)}, ${size(picked)} lines: --full shows ${all.length === 1 ? "it" : "them"})`];
    notes.set(line, all);
    return base.flatMap((b) => (b === picked[0] ? [line] : picked.includes(b) ? [] : [b]));
  };
  const long = (b: string[]) => b.length > 1 && names(b).length > 0 && !notes.has(b);
  // 2. the contract instances, all of them
  const isContract = (b: string[]) => long(b) && names(b).every((n) => /^hcontract/.test(n));
  hyps = collapsed(hyps, hyps.filter(isContract), ":", "contract instance", "contract instances");
  if (size(head) + size(hyps) + size(rest) <= maxLines) return [...head, ...hyps, ...rest].flat().join("\n");
  if (ti < 0) return [...head, ...hyps].flat().slice(0, maxLines).join("\n") + "\n  …";
  // the conclusion, at most 3 lines; what follows it (after a timeout without a failing case: how
  // far the cases got), at most 2
  const target = rest[0].length > 3 ? [...rest[0].slice(0, 3), "  …"] : rest[0];
  const after = rest.slice(1).flat();
  const tail = after.length <= 2 ? after : ["  …"];
  const over = (hs: string[][]) => size(head) + size(hs) + target.length + tail.length - maxLines;
  const shown = () => [...head.flat(), ...hyps.flat(), ...target, ...tail].join("\n");
  if (over(hyps) <= 0) return shown();
  // 3. let-definitions: `x : T :=` (at the top level of the line: not the `:=` of a structure
  // instance `{ f := … }` in a hypothesis's type), from the top, as many as needed
  const isDef = (b: string[]) => {
    const m = /^(?:[^\s:]+ )*[^\s:]+ : /.exec(b[0]);
    if (!m) return false;
    const s = b[0].slice(m[0].length);
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
      if ("([{⟨".includes(s[i])) depth++;
      else if (")]}⟩".includes(s[i])) depth--;
      else if (depth === 0 && s.startsWith(" :=", i) && (i + 3 === s.length || s[i + 3] === " ")) return true;
    }
    return false;
  };
  const defs = hyps.filter((b) => long(b) && isDef(b));
  const before = hyps;
  for (let k = 1; k <= defs.length; k++) {
    hyps = collapsed(before, defs.slice(0, k), ":=", "definition", "definitions");
    if (over(hyps) <= 0) return shown();
  }
  // 4. the other long hypotheses, from the top, each one whose line frees no more lines than are
  // still needed; not the one right above the conclusion (the last case split, often the negated
  // goal: the one that decides) when it fits, which step 5 then shows whole
  const room = Math.max(0, maxLines - size(head) - target.length - tail.length);
  const base = hyps;
  const last = base[base.length - 1];
  const picked: string[][] = [];
  for (const b of base.filter(long)) {
    if (b === last && b.length <= room - 1) continue;
    const trial = collapsed(base, [...picked, b], ":", "long hypothesis", "long hypotheses");
    if (size(hyps) - size(trial) > over(hyps)) continue;
    picked.push(b);
    hyps = trial;
    if (over(hyps) <= 0) return shown();
  }
  // 5. the lines that stand for others (when they fit), then from the conclusion up each
  // hypothesis whole while it fits, a long one that does not as one line that names it, until
  // one does not fit at all; one line names and counts the hypotheses left out (if any)
  const keep = new Map<string[], string[]>();
  let left = room - 1;
  const standIns = hyps.filter((b) => notes.has(b));
  if (size(standIns) <= left) {
    for (const b of standIns) keep.set(b, b);
    left -= size(standIns);
  }
  for (let i = hyps.length - 1; i >= 0; i--) {
    const b = hyps[i];
    if (keep.has(b)) continue;
    if (b.length <= left) {
      keep.set(b, b);
      left -= b.length;
    } else if (long(b) && left >= 1) {
      keep.set(b, collapsed([b], [b], ":", "long hypothesis", "long hypotheses")[0]);
      left -= 1;
    } else break;
  }
  const dropped = hyps.filter((b) => !keep.has(b));
  const ns = dropped.flatMap(names);
  const what = ns.length ? `${a(ns.length, "earlier hypothesis", "earlier hypotheses")}: ${[...ns.slice(0, 8), ...(ns.length > 8 ? ["…"] : [])].join(", ")}` : a(size(dropped), "earlier line", "earlier lines");
  const marker = dropped.length ? [`  … (${what}: --full shows ${ns.length === 1 ? "it" : "them"})`] : [];
  return [...head.flat(), ...marker, ...hyps.flatMap((b) => keep.get(b) ?? []), ...target, ...tail].join("\n");
}
