// Runs the case's next() and the contract functions of vreact/spec's runtime (argv[2]) in a
// global environment like a browser page's, where HTML's named access on Window answers every
// string name the window lacks with an element (a named properties object in the prototype chain
// of the global object). Exits 1 if anything throws or returns a wrong value.
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";

const [specPath, project] = process.argv.slice(2);
const spec = await import(pathToFileURL(specPath).href);
const compile = (f) => ts.transpileModule(fs.readFileSync(f, "utf8"), { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, jsx: ts.JsxEmit.ReactJSX, esModuleInterop: true }, fileName: f }).outputText;
const code = compile(path.join(project, "src", "M.tsx"));

class HTMLElementLike { constructor(id) { this.id = id; this.tagName = "H2"; } }
const real = Object.getPrototypeOf(globalThis);
const named = new Proxy(real, {
  get: (t, k, r) => (typeof k === "string" && !(k in t) ? new HTMLElementLike(k) : Reflect.get(t, k, r)),
  has: (t, k) => typeof k === "string" || k in t,
});
const fails = [];
const check = (what, f) => {
  try {
    f();
  } catch (e) {
    fails.push(`${what}: ${e?.constructor?.name}: ${e?.message}`);
  }
};
Object.setPrototypeOf(globalThis, named);
try {
  check("named access is emulated", () => {
    if (!(globalThis.__VREACT_TEST__ instanceof HTMLElementLike)) throw new Error("no element under a string global");
  });
  const mod = { exports: {} };
  new Function("exports", "require", "module", code)(mod.exports, (s) => (s === "vreact/spec" ? spec : {}), mod);
  check("next(1)", () => {
    const r = mod.exports.next(1);
    if (r !== 2) throw new Error(`returned ${r}`);
  });
  check("requires(true)", () => spec.requires(true));
  check("ensures(…)", () => spec.ensures(() => true));
  check("assert(true)", () => spec.assert(true));
  check("invariant(true)", () => spec.invariant(true));
  check("hole() outside synth", () => {
    try {
      spec.hole();
    } catch (e) {
      if (e instanceof Error && e.message.startsWith("vreact: unfilled hole()")) return;
      throw e;
    }
    throw new Error("hole() returned");
  });
} finally {
  Object.setPrototypeOf(globalThis, real);
}
if (fails.length) {
  console.log(fails.join("\n"));
  process.exit(1);
}
console.log("ok");
