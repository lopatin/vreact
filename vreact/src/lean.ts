/** Running Lean on the generated project and mapping results back to TypeScript. */
import { spawnSync } from "node:child_process";
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

export function runLake(outDir: string): { messages: LeanMessage[]; raw: string; status: number } {
  const bin = leanBin();
  const env = { ...process.env, PATH: bin ? `${bin}:${process.env.PATH}` : process.env.PATH };
  const r = spawnSync("lake", ["build"], { cwd: outDir, env, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 });
  if (r.error) throw new Error(`could not run lake (is Lean installed? see SKILL.md): ${r.error.message}`);
  const raw = (r.stdout ?? "") + (r.stderr ?? "");
  const status = r.status ?? 1;
  const messages = parseMessages(raw);
  // a failed build must never be read as "nothing to report"
  if (status !== 0 && !messages.some((m) => m.severity === "error")) {
    const tail = raw.trim().split("\n").slice(-12).join("\n");
    messages.push({ severity: "error", file: "", line: 0, col: 0, text: `lake build failed (exit ${status}${r.signal ? `, ${r.signal}` : ""})${tail ? ":\n" + tail : ""}` });
  }
  return { messages, raw, status };
}

const HEAD = /^(error|warning|info): (.+?\.lean):(\d+):(\d+): ?(.*)$/;
/** Lake/Lean errors without a position: bad import, build cycle, missing file, lakefile, … */
const HEAD_NOPOS = /^error: (?:(.+?\.lean): )?(.*)$/;
/** Crashes of the Lean process itself. */
const PANIC = /^(PANIC|INTERNAL PANIC|uncaught exception|libc\+\+abi|Stack overflow|Segmentation fault)\b/;
const STOP = /^(error|warning|info|trace|✖|⚠|✔|ℹ|Some required targets|Build completed|- )/;

export function parseMessages(raw: string): LeanMessage[] {
  const out: LeanMessage[] = [];
  let cur: LeanMessage | null = null;
  let generic: LeanMessage | null = null;
  for (const line of raw.split("\n")) {
    const m = HEAD.exec(line);
    if (m) {
      if (cur) out.push(cur);
      cur = { severity: m[1] as LeanMessage["severity"], file: m[2], line: +m[3], col: +m[4], text: m[5] };
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

/** Locate the `/-⟦obN⟧-/` markers in the generated files. */
export function findMarkers(outDir: string): Marker[] {
  const markers: Marker[] = [];
  const walk = (d: string) => {
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
  walk(outDir);
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

const DECL_KW = /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|axiom|structure|inductive|instance|example|opaque|class)\b\s*([^\s:({[⦃]*)/;
const CMD_KW = /^(\/--|@\[|#[a-z]|namespace\b|end\b|section\b|noncomputable section\b|open\b|set_option\b|import\b|attribute\b|deriving instance\b|macro_rules\b|macro\b|syntax\b|elab\b|grind_pattern\b|universe\b|variable\b|mutual\b)/;

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

/** A runtime limit hit outside `vreact_ob` (which reports its own as an ordinary failure): the declaration was aborted. */
const ABORT = /\(deterministic\) timeout|maximum recursion depth has been reached/;
const isAbort = (text: string) => ABORT.test(text) && !text.startsWith("vreact:");
const BUILD = /bad import|unknown module prefix|build cycle|no such file|does not exist|import .* failed|environment already contains|object file|lakefile|unknown package|failed to (?:load|read|fetch)/;
const FOLLOW_ON = /Unknown (?:identifier|constant)|unknown (?:identifier|constant)/;
/** The sentinel `#eval "vreact:checked"` that ends every generated file: Lean got to the end of it. */
const SENTINEL = /^"vreact:checked"$/;

export interface Verdict {
  proved: Obligation[];
  failed: { ob: Obligation; message: string }[];
  /** obligations whose proof was not (or not completely) checked; see `reasons` */
  unchecked: Obligation[];
  /** errors not attributable to a single obligation (each with its `cause`) */
  internal: LeanMessage[];
  axioms: Map<string, string[]>;
  /** why an obligation in `unchecked` was not established */
  reasons: Map<number, string>;
  /** generated declarations that did not elaborate cleanly: name → first error */
  declErrors: Map<string, string>;
  /** `declaration uses 'sorry'` warnings in generated files and user proofs */
  sorries: LeanMessage[];
  /** generated files Lean elaborated to the end */
  checkedFiles: Set<string>;
}

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
 * An obligation counts as proved only if its file was elaborated to the end (the
 * `vreact:checked` sentinel was printed), no error was reported at its marker, and its
 * declaration has no other error: an error elsewhere in the declaration (a timeout at the
 * declaration start, an elaboration error, an aborting runtime limit) means Lean may never
 * have finished the obligation. Lake errors without a position are kept as `build` errors.
 */
export function judge(obligations: Obligation[], messages: LeanMessage[], markers: Marker[], outDir: string, _built?: Set<string>): Verdict {
  const decls = findDecls(outDir);
  const failedIds = new Map<number, string>();
  const internal: LeanMessage[] = [];
  const axioms = new Map<string, string[]>();
  const checkedFiles = new Set<string>();
  const sorries: LeanMessage[] = [];
  const declErrors = new Map<string, string>();
  /** per declaration: unattributed errors, and whether a runtime limit aborted it */
  const bad = new Map<LeanDecl, { errs: LeanMessage[]; aborted: boolean; failedObs: number }>();
  const badOf = (d: LeanDecl) => bad.get(d) ?? (bad.set(d, { errs: [], aborted: false, failedObs: 0 }), bad.get(d)!);
  const generated = (rel: string) => decls.has(rel);
  const firstErrLine = new Map<string, number>();
  for (const msg of messages) {
    const rel = msg.file && path.isAbsolute(msg.file) ? path.relative(outDir, msg.file) : msg.file;
    msg.file = rel;
    const d = msg.line ? declAt(decls.get(rel), msg.line) : undefined;
    msg.decl = d?.name ?? null;
    if (msg.severity === "info") {
      // (Lean names may themselves contain `'`, e.g. `VTS.m.max'`)
      const am = /^'(.+?)' depends on axioms: \[([^\]]*)\]/.exec(msg.text);
      if (am) axioms.set(am[1], am[2].split(",").map((s) => s.trim()).filter(Boolean));
      const none = /^'(.+?)' does not depend on any axioms/.exec(msg.text);
      if (none) axioms.set(none[1], []);
      if (SENTINEL.test(msg.text.trim())) checkedFiles.add(rel);
      continue;
    }
    if (msg.severity === "warning") {
      if (generated(rel) && /declaration uses [`']sorry[`']/.test(msg.text)) sorries.push(msg);
      continue;
    }
    if (generated(rel) && msg.line && (firstErrLine.get(rel) ?? Infinity) > msg.line) firstErrLine.set(rel, msg.line);
    if (d?.name && !declErrors.has(d.name)) declErrors.set(d.name, msg.text);
    // the marker on that line closest to the left of the error column
    const cands = markers.filter((mk) => mk.file === rel && mk.line === msg.line && mk.col <= msg.col && msg.col <= mk.col + 40);
    const mk = cands.length ? cands.reduce((a, b) => (b.col > a.col ? b : a)) : null;
    if (mk && mk.id !== 0) {
      if (!failedIds.has(mk.id)) failedIds.set(mk.id, msg.text);
      if (d) {
        badOf(d).failedObs++;
        if (isAbort(msg.text)) badOf(d).aborted = true;
      }
      continue;
    }
    if (d) badOf(d).errs.push(msg);
    internal.push(msg);
  }
  // classify the unattributed errors
  for (const msg of internal) {
    msg.cause =
      PANIC.test(msg.text) ? "internal"
      : !msg.file || !msg.line || (BUILD.test(msg.text) && !msg.decl) ? "build"
      : msg.file.startsWith("Proofs" + path.sep) || msg.file.startsWith("Proofs/") ? "proof"
      : isAbort(msg.text) ? "timeout"
      : FOLLOW_ON.test(msg.text) && (firstErrLine.get(msg.file) ?? Infinity) < msg.line ? "follow-on"
      : "internal";
  }
  const proved: Obligation[] = [];
  const failed: { ob: Obligation; message: string }[] = [];
  const unchecked: Obligation[] = [];
  const reasons = new Map<number, string>();
  const markerOf = new Map(markers.map((mk) => [mk.id, mk]));
  const pending = new Map<LeanDecl, Obligation[]>();
  for (const ob of obligations) {
    const f = failedIds.get(ob.id);
    const mk = markerOf.get(ob.id);
    if (f !== undefined) {
      failed.push({ ob, message: f });
      continue;
    }
    if (!mk) {
      unchecked.push(ob);
      reasons.set(ob.id, "its proof is missing from the generated Lean (translator bug)");
      internal.push({ severity: "error", file: "", line: 0, col: 0, text: `obligation ${ob.where} [${ob.kind}] is missing from the generated Lean`, cause: "internal" });
      continue;
    }
    if (!checkedFiles.has(mk.file)) {
      unchecked.push(ob);
      reasons.set(ob.id, `${mk.file} was not checked: a module it imports failed, or the file stopped at an error in its imports`);
      continue;
    }
    const d = declAt(decls.get(mk.file), mk.line);
    const b = d && bad.get(d);
    if (d && b && (b.errs.length || b.aborted)) {
      pending.set(d, [...(pending.get(d) ?? []), ob]);
      continue;
    }
    proved.push(ob);
  }
  // obligations of declarations that failed for a reason Lean did not report at a marker
  for (const [d, obs] of pending) {
    const b = bad.get(d)!;
    const err = b.errs[0];
    const why = err ? err.text.split("\n")[0] : "a runtime limit aborted the declaration";
    const where = err ? `${err.file}:${err.line}:${err.col}` : d.file;
    const dn = d.name ?? `the declaration at ${d.file}:${d.start}`;
    if (obs.length === 1 && b.failedObs === 0 && err) failed.push({ ob: obs[0], message: `error in the declaration of this obligation (${dn}) at ${where}:\n${err.text}` });
    else
      for (const ob of obs) {
        unchecked.push(ob);
        reasons.set(ob.id, `${dn} did not elaborate (${why}), so Lean may not have finished this obligation`);
      }
  }
  return { proved, failed, unchecked, internal, axioms, reasons, declErrors, sorries, checkedFiles };
}

/** Keep the informative part of a Lean failure (the goal). */
export function summarizeLeanError(text: string, maxLines = 30): string {
  const lines = text.split("\n");
  const cut = lines.findIndex((l) => /\[grind\] Goal diagnostics|\[grind\] Diagnostics/.test(l));
  const kept = (cut > 0 ? lines.slice(0, cut) : lines).filter((l) => l.trim() !== "");
  return kept.slice(0, maxLines).join("\n") + (kept.length > maxLines ? "\n  …" : "");
}
