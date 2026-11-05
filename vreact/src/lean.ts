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
  return { messages: lakeMessages(raw, status, r.signal), raw, status };
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
const CMD_KW = /^(\/--|@\[|#[a-z]+(?=\s|$)|(?:namespace|end|section|noncomputable section|open|set_option|import|attribute|deriving instance|macro_rules|macro|syntax|elab|grind_pattern|universe|variable|mutual)(?=\s|$))/;

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
 * was admitted), or blocked (a warning: it failed on a goal that depends on `sorry` from
 * elsewhere, so it was not really checked; the goal was admitted)
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
  /** obligations in `unchecked` that `vreact_ob` could not check: their goal depends on `sorry` from elsewhere */
  blocked: Set<number>;
}

/** `#print axioms X` (the generator writes one per line) */
const PRINT_AXIOMS = /^#print axioms (\S+)\s*$/;
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
 * a warning `vreact:blocked <why>` when it failed on a goal that depends on `sorry` from
 * elsewhere (then the obligation is not checked rather than failed); in both cases the goal is
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
 * sentinel position in a generated file (a user proof cannot fake them by printing the same
 * text); a result at the marker of no known obligation is not an obligation's.
 */
export function judge(obligations: Obligation[], messages: LeanMessage[], markers: Marker[], outDir: string, _built?: Set<string>): Verdict {
  const decls = findDecls(outDir);
  const failedIds = new Map<number, string>();
  /** the marker copies with positive evidence */
  const okMarkers = new Set<Marker>();
  /** obligations `vreact_ob` could not check (their goal depends on `sorry` from elsewhere) */
  const blockedIds = new Map<number, string>();
  /** declarations with a failed or blocked obligation copy (their `sorry` is the admitted goal) */
  const failedDecls = new Set<LeanDecl>();
  const internal: LeanMessage[] = [];
  const axioms = new Map<string, string[]>();
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
    msg.cause =
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
      reasons.set(ob.id, `its goal depends on \`sorry\` from a failure elsewhere (a failed obligation, a declaration with an error, or a hole()), so Lean could not check it: fix that first`);
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
  // the `sorry` warning of a declaration with a failed obligation is that obligation's
  // admitted goal (reported as the failure), not a hole
  const admitted = (s: LeanMessage) => {
    const d = s.line ? declAt(decls.get(s.file), s.line) : undefined;
    return !!d && failedDecls.has(d);
  };
  return { proved, failed, unchecked, internal, axioms, reasons, declErrors, brokenDecls, sorries: sorries.filter((s) => !admitted(s)), checkedFiles, blocked: blockedObs };
}

/** Keep the informative part of a Lean failure (the goal). */
export function summarizeLeanError(text: string, maxLines = 30): string {
  const lines = text.split("\n");
  const cut = lines.findIndex((l) => /\[grind\] Goal diagnostics|\[grind\] Diagnostics/.test(l));
  const kept = (cut > 0 ? lines.slice(0, cut) : lines).filter((l) => l.trim() !== "");
  return kept.slice(0, maxLines).join("\n") + (kept.length > maxLines ? "\n  …" : "");
}
