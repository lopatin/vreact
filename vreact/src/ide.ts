/**
 * Lean editor support for an app folder. A Lean editor opened on the app folder (lean4ij in
 * WebStorm/IntelliJ, the Lean 4 extension of VS Code) needs `lean-toolchain` at the project
 * root and runs `lake serve` there. Next to vreact.json, vreact writes
 *   lean-toolchain  the Lean version of the VReact library (tool/lean/lean-toolchain)
 *   lakefile.toml   a Lake package that requires the generated project (`out`, package `vts`)
 * so that the proof files resolve `import VTS.<module>.Defs` against the last `vreact verify`.
 * The first line of the lakefile marks it as vreact's: only then are both files rewritten (to
 * follow the library's toolchain and the "out" directory). A lakefile.toml without that line,
 * or any lakefile.lean, is the user's: vreact never writes either of the two files then.
 *
 * Also a script (for setup.sh): node --experimental-strip-types ide.ts <app folder>
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

export const LAKEFILE_MARKER = "# vreact: Lean editor support";

/** what Lake writes next to the lakefile (the manifest names the VReact library by absolute path) */
const IGNORED = [".lake/", "lake-manifest.json"];

export interface EditorProject {
  /** what was written or removed, one line each (nothing when everything was up to date) */
  notes: string[];
  /** the user's own lakefile (never written), relative to the app folder */
  userLakefile: string | null;
  /** whether the user's lakefile requires the package `vts` at the generated project (`out`) */
  requiresOut: boolean;
}

export function editorProject(root: string, outDir: string, proofsDir: string, leanLib: string): EditorProject {
  root = path.resolve(root);
  const res: EditorProject = { notes: [], userLakefile: null, requiresOut: false };
  // `"out": "."`: the generated project is the app folder itself
  if (path.resolve(outDir) === root) return res;
  for (const f of ["lakefile.lean", "lakefile.toml"]) {
    const p = path.join(root, f);
    if (fs.existsSync(p) && (f === "lakefile.lean" || !fs.readFileSync(p, "utf8").startsWith(LAKEFILE_MARKER))) {
      res.userLakefile = f;
      res.requiresOut = requiresPackage(p, "vts", outDir);
      return res;
    }
  }
  const rel = (p: string) => path.relative(root, p).split(path.sep).join("/") || ".";
  const out = rel(outDir);
  const lakefile = [
    `${LAKEFILE_MARKER} (written by vreact, which keeps this file and lean-toolchain up to date while this line is here)`,
    `# Open this folder as the editor's project and run \`vreact verify\` once: ${rel(proofsDir)}/*.lean then`,
    `# resolve \`import VTS.<module>.Defs\` through the Lean project that \`vreact verify\` generates in`,
    `# ${out}/ (as of its last run; \`vreact verify\` stays the source of truth). Delete the first line`,
    `# to manage this file and lean-toolchain yourself.`,
    `name = "app"`,
    ``,
    `[[require]]`,
    `name = "vts"`,
    `path = ${JSON.stringify(out)}`,
    ``,
  ].join("\n");
  const toolchain = fs.readFileSync(path.join(leanLib, "lean-toolchain"), "utf8");
  const lakefilePath = path.join(root, "lakefile.toml");
  const created = !fs.existsSync(lakefilePath);
  const wrote: string[] = [];
  for (const [f, text] of [["lakefile.toml", lakefile], ["lean-toolchain", toolchain]]) {
    const p = path.join(root, f);
    if (fs.existsSync(p) && fs.readFileSync(p, "utf8") === text) continue;
    fs.writeFileSync(p, text);
    wrote.push(f);
  }
  if (wrote.length) res.notes.push(`${created ? "wrote" : "updated"} ${wrote.join(" and ")} (Lean editor support: open ${root} as the editor's project)`);
  // a manifest that names other directories (the tool or the app moved, another "out") would
  // keep lake on them: lake writes a new one from the lakefile
  const manifest = path.join(root, "lake-manifest.json");
  if (fs.existsSync(manifest) && !manifestMatches(manifest, { vts: outDir, VReact: leanLib })) {
    fs.rmSync(manifest, { force: true });
    res.notes.push("removed lake-manifest.json (it named other directories; lake writes a new one)");
  }
  if (created) {
    const added = ensureIgnored(path.join(root, ".gitignore"));
    if (added.length) res.notes.push(`added ${added.join(", ")} to .gitignore`);
  }
  return res;
}

/**
 * Whether a lakefile requires the package `name` from the directory `dir`: a `[[require]]` table
 * of a lakefile.toml with `name = "…"` and `path = "…"`, or `require name from "…"` in a
 * lakefile.lean (false when it cannot be read, or says it some other way).
 */
export function requiresPackage(lakefile: string, name: string, dir: string): boolean {
  let text: string;
  try {
    text = fs.readFileSync(lakefile, "utf8");
  } catch {
    return false;
  }
  const same = (p: string) => {
    const a = path.resolve(path.dirname(lakefile), p);
    const b = path.resolve(dir);
    if (a === b) return true;
    try {
      return fs.realpathSync(a) === fs.realpathSync(b);
    } catch {
      return false;
    }
  };
  if (lakefile.endsWith(".lean")) {
    const re = /^\s*require\s+(?:«([^»]+)»|([\w.]+))\s+from\s+"([^"]*)"/gm;
    for (const m of text.matchAll(re)) if ((m[1] ?? m[2]) === name && same(m[3])) return true;
    return false;
  }
  // lakefile.toml: the key/value lines of each [[require]] table (basic or literal strings)
  const str = (v: string) => /^"((?:[^"\\]|\\.)*)"\s*(?:#.*)?$/.exec(v)?.[1].replace(/\\(.)/g, "$1") ?? /^'([^']*)'\s*(?:#.*)?$/.exec(v)?.[1] ?? null;
  let table: Record<string, string | null> | null = null;
  const tables: Record<string, string | null>[] = [];
  for (const raw of text.split(/\r?\n/)) {
    const l = raw.trim();
    if (l.startsWith("[")) {
      table = /^\[\[\s*require\s*\]\]\s*(?:#.*)?$/.test(l) ? {} : null;
      if (table) tables.push(table);
      continue;
    }
    const kv = /^([A-Za-z0-9_-]+|"[^"]*")\s*=\s*(.*)$/.exec(l);
    if (table && kv) table[kv[1].replace(/^"|"$/g, "")] = str(kv[2]);
  }
  return tables.some((t) => t.name === name && typeof t.path === "string" && same(t.path));
}

/** Whether a lake manifest names each package of `deps` at that directory (false when it cannot be read). */
export function manifestMatches(manifest: string, deps: Record<string, string>): boolean {
  try {
    const m = JSON.parse(fs.readFileSync(manifest, "utf8")) as { packages?: { name?: string; dir?: string }[] };
    return Object.entries(deps).every(([name, dir]) => {
      const dep = (m.packages ?? []).find((p) => p.name === name);
      return !!dep?.dir && fs.realpathSync(path.resolve(path.dirname(manifest), dep.dir)) === fs.realpathSync(dir);
    });
  } catch {
    return false;
  }
}

/** Appends the entries of `IGNORED` that the file lacks (in any spelling: `/.lake`, `.lake`, …); returns them. */
function ensureIgnored(file: string): string[] {
  const text = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
  const norm = (l: string) => l.trim().replace(/^(\*\*\/|\/)/, "").replace(/\/$/, "");
  const have = new Set(text.split(/\r?\n/).map(norm));
  const missing = IGNORED.filter((e) => !have.has(norm(e)));
  if (missing.length) fs.writeFileSync(file, text + (text && !text.endsWith("\n") ? "\n" : "") + missing.join("\n") + "\n");
  return missing;
}

// (setup.sh reaches this file through the skill's `tool` symlink; Node runs it at its real path)
if (process.argv[1] && fs.realpathSync(process.argv[1]) === fs.realpathSync(fileURLToPath(import.meta.url))) {
  const root = path.resolve(process.argv[2] ?? ".");
  const cfgFile = path.join(root, "vreact.json");
  let pc: { out?: unknown; proofs?: unknown } = {};
  try {
    if (fs.existsSync(cfgFile)) pc = JSON.parse(fs.readFileSync(cfgFile, "utf8"));
  } catch (e) {
    console.error(`error: ${cfgFile} is not valid JSON: ${e instanceof Error ? e.message : e}`);
    process.exit(1);
  }
  const str = (v: unknown, d: string) => (typeof v === "string" ? v : d);
  const leanLib = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "lean");
  const r = editorProject(root, path.resolve(root, str(pc.out, ".vreact")), path.resolve(root, str(pc.proofs, "proofs")), leanLib);
  for (const n of r.notes) console.log(`  ${n}`);
  // (only when the user's lakefile does not already require it)
  if (r.userLakefile && !r.requiresOut) console.log(`  kept your ${r.userLakefile}: for Lean editor support it needs a [[require]] of the package "vts" at ${str(pc.out, ".vreact")}`);
}
