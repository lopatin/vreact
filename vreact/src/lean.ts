/** Running Lean on the generated project and mapping results back to TypeScript. */
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import type { Obligation } from "./ctx.ts";

export interface LeanMessage {
  severity: "error" | "warning" | "info";
  file: string;
  line: number;
  col: number;
  text: string;
}

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
  return { messages: parseMessages(raw), raw, status: r.status ?? 1 };
}

const HEAD = /^(error|warning|info): (.+?\.lean):(\d+):(\d+): ?(.*)$/;
const STOP = /^(error|warning|info|trace|✖|⚠|✔|Some required targets|Build completed|- )/;

export function parseMessages(raw: string): LeanMessage[] {
  const out: LeanMessage[] = [];
  let cur: LeanMessage | null = null;
  for (const line of raw.split("\n")) {
    const m = HEAD.exec(line);
    if (m) {
      if (cur) out.push(cur);
      cur = { severity: m[1] as LeanMessage["severity"], file: m[2], line: +m[3], col: +m[4], text: m[5] };
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

export interface Verdict {
  proved: Obligation[];
  failed: { ob: Obligation; message: string }[];
  unchecked: Obligation[];
  internal: LeanMessage[];
  axioms: Map<string, string[]>;
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

/** Attribute Lean errors to obligations. */
export function judge(obligations: Obligation[], messages: LeanMessage[], markers: Marker[], outDir: string, built?: Set<string>): Verdict {
  const failedIds = new Map<number, string>();
  const internal: LeanMessage[] = [];
  const axioms = new Map<string, string[]>();
  const builtFiles = new Set<string>();
  for (const msg of messages) {
    const rel = path.isAbsolute(msg.file) ? path.relative(outDir, msg.file) : msg.file;
    builtFiles.add(rel);
    if (msg.severity === "info") {
      const am = /'([^']+)' depends on axioms: \[([^\]]*)\]/.exec(msg.text);
      if (am) axioms.set(am[1], am[2].split(",").map((s) => s.trim()).filter(Boolean));
      const none = /'([^']+)' does not depend on any axioms/.exec(msg.text);
      if (none) axioms.set(none[1], []);
      continue;
    }
    if (msg.severity !== "error") continue;
    // the marker on that line closest to the left of the error column
    const cands = markers.filter((mk) => mk.file === rel && mk.line === msg.line && mk.col <= msg.col && msg.col <= mk.col + 40);
    const mk = cands.length ? cands.reduce((a, b) => (b.col > a.col ? b : a)) : null;
    if (mk && mk.id !== 0) {
      if (!failedIds.has(mk.id)) failedIds.set(mk.id, msg.text);
    } else internal.push(msg); // no obligation there, or a generated (non-obligation) proof: internal error
  }
  const proved: Obligation[] = [];
  const failed: { ob: Obligation; message: string }[] = [];
  const unchecked: Obligation[] = [];
  const markerFile = new Map(markers.map((mk) => [mk.id, mk.file]));
  // files that never reported anything may not have been built (dependency failure)
  for (const ob of obligations) {
    const f = failedIds.get(ob.id);
    const file = markerFile.get(ob.id);
    const mod = file ? file.replace(/\.lean$/, "").split(path.sep).join(".") : "";
    if (f !== undefined) failed.push({ ob, message: f });
    else if (file && !builtFiles.has(file)) unchecked.push(ob);
    else proved.push(ob);
  }
  return { proved, failed, unchecked, internal, axioms };
}

/** Keep the informative part of a Lean failure (the goal). */
export function summarizeLeanError(text: string, maxLines = 30): string {
  const lines = text.split("\n");
  const cut = lines.findIndex((l) => /\[grind\] Goal diagnostics|\[grind\] Diagnostics/.test(l));
  const kept = (cut > 0 ? lines.slice(0, cut) : lines).filter((l) => l.trim() !== "");
  return kept.slice(0, maxLines).join("\n") + (kept.length > maxLines ? "\n  …" : "");
}
