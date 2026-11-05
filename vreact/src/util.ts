import ts from "typescript";
import path from "node:path";

/** A diagnostic attached to a TypeScript source location. */
export class VtsError extends Error {
  file: string;
  line: number;
  col: number;
  constructor(node: ts.Node | undefined, message: string) {
    super(message);
    if (node && node.getSourceFile()) {
      const sf = node.getSourceFile();
      const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
      this.file = sf.fileName;
      this.line = line + 1;
      this.col = character + 1;
    } else {
      this.file = "";
      this.line = 0;
      this.col = 0;
    }
  }
}

export function fail(node: ts.Node | undefined, message: string): never {
  throw new VtsError(node, message);
}

export function loc(node: ts.Node): { file: string; line: number; col: number } {
  const sf = node.getSourceFile();
  const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
  return { file: sf.fileName, line: line + 1, col: character + 1 };
}

export function relLoc(node: ts.Node, root: string): string {
  const l = loc(node);
  return `${path.relative(root, l.file)}:${l.line}:${l.col}`;
}

export function nodeText(node: ts.Node, max = 80): string {
  const t = node.getText().replace(/\s+/g, " ");
  return t.length > max ? t.slice(0, max - 1) + "…" : t;
}

const LEAN_KEYWORDS = new Set([
  "fun", "at", "by", "have", "show", "from", "match", "with", "do", "then", "else", "if", "let", "in",
  "end", "open", "namespace", "section", "structure", "class", "instance", "where", "deriving", "def",
  "theorem", "example", "import", "variable", "universe", "mutual", "inductive", "local", "private",
  "protected", "partial", "unsafe", "macro", "syntax", "notation", "calc", "sorry", "Type", "Prop",
  "Sort", "forall", "exists", "this", "return", "for", "unless", "mut", "try", "catch", "finally",
  "break", "continue", "abbrev", "axiom", "lemma", "opaque", "noncomputable", "attribute", "set_option",
  "hiding", "renaming", "export", "infix", "infixl", "infixr", "prefix", "postfix", "omit", "include",
  "termination_by", "decreasing_by", "suffices", "obtain", "nomatch", "nofun", "fun", "λ", "Σ", "Π",
  "true", "false", "none", "some", "id", "True", "False", "Nat", "Int", "String", "Bool", "List", "Option",
  "Float", "Unit", "Prod", "decide", "not", "and", "or", "max", "min", "toString", "rfl", "trivial",
]);

/** A Lean identifier for a TypeScript identifier (locals, params). */
export function leanIdent(name: string): string {
  if (LEAN_KEYWORDS.has(name)) return name + "'";
  if (/^[A-Za-z_][A-Za-z0-9_']*$/.test(name)) return name;
  return "«" + name + "»";
}

/** A Lean identifier for a structure field / constructor (guillemet-quoted when needed). */
export function leanField(name: string): string {
  if (LEAN_KEYWORDS.has(name)) return "«" + name + "»";
  if (/^[A-Za-z_][A-Za-z0-9_']*$/.test(name)) return name;
  return "«" + name + "»";
}

/** A Lean string literal. */
export function leanStr(s: string): string {
  let out = '"';
  for (const ch of s) {
    const c = ch.codePointAt(0)!;
    if (ch === '"') out += '\\"';
    else if (ch === "\\") out += "\\\\";
    else if (ch === "\n") out += "\\n";
    else if (ch === "\t") out += "\\t";
    else if (ch === "\r") out += "\\r";
    else if (c < 0x20 || c === 0x7f) out += "\\x" + c.toString(16).padStart(2, "0");
    else out += ch;
  }
  return out + '"';
}

/** A JavaScript string value (UTF-16 code units) for a source literal. */
export function jsStr(s: string): string {
  return s === "" ? "(VReact.JS.Str.ofString \"\")" : `(VReact.JS.Str.ofString ${leanStr(s)})`;
}

/** Lean integer literal (parenthesised when negative). */
export function leanInt(n: number | bigint): string {
  const s = n.toString();
  return s.startsWith("-") ? `(${s})` : s;
}

export function paren(s: string): string {
  if (/^[A-Za-z0-9_'.«»]+$/.test(s) || /^\(.*\)$/s.test(s) && balanced(s.slice(1, -1))) return s;
  if (/^"([^"\\]|\\.)*"$/.test(s)) return s;
  return `(${s})`;
}

function balanced(s: string): boolean {
  let d = 0;
  let inStr = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (inStr) {
      if (c === "\\") i++;
      else if (c === '"') inStr = false;
      continue;
    }
    if (c === '"') inStr = true;
    else if (c === "(") d++;
    else if (c === ")") {
      d--;
      if (d < 0) return false;
    }
  }
  return d === 0;
}

/** Indent every line of `s` by `n` spaces. */
export function indent(s: string, n = 2): string {
  const pad = " ".repeat(n);
  return s
    .split("\n")
    .map((l) => (l.length ? pad + l : l))
    .join("\n");
}

export function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}
