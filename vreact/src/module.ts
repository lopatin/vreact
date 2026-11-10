/**
 * Program-level driver: loads the TypeScript program, checks it, collects
 * declarations, and emits one Lean project with two files per TS module:
 *
 *   VTS/<Mod>/Defs.lean — types, constants, pure functions (+ inline obligations), each
 *                         function followed by its postconditions (usable by later bodies)
 *   VTS/<Mod>/Posts.lean — (only with a `proofs/<Mod>.lean`) the postconditions of the
 *                         functions nothing else in Defs.lean uses, so that the lemmas help them
 *   VTS/<Mod>/View.lean — component specs and renders, root certificates
 *
 * User lemmas in `proofs/<Mod>.lean` sit after Defs (they may mention the definitions and are
 * available to the postconditions in Posts, to every obligation of the views, and to the Defs
 * of every module importing <Mod>); `proofs/Base.lean` is imported by every Defs. Each file
 * ends with `#print axioms` and `#vreact_assumed` for every declaration it reports and the
 * `vreact:checked` sentinel.
 */
import ts from "typescript";
import fs from "node:fs";
import path from "node:path";
import { Program, ModCtx, SPEC_MODULE, moduleFile, isErasedType, type Obligation, type FnInfo, type CompInfo, type Global, type ConstInfo, type HoleEnv } from "./ctx.ts";
import { T, type VType, typeOfNode, typeOfDecl, emitTypeDecl, leanType, nonValuePart, checkValueType, registerTypeParams, showType } from "./types.ts";
import { VtsError, fail, leanIdent, leanField, leanStr, paren, capitalize, nodeText, exprText, clashesWithLean } from "./util.ts";
import { LEAN_TYPE_AUX, LEAN_ROOT_NAMES } from "./leanNames.ts";
import { expr, prop, propAll, valueBlock, specFn, symbolOf, bindParam, typeOf, checkParamAnnotation, checkNotThisParam, checkClosures } from "./translate.ts";
import { translateComponent, compSignature, baseEnv } from "./component.ts";
import { leanDecls, checkProofFiles } from "./lean.ts";
import { manifestMatches } from "./ide.ts";

export interface Config {
  root: string;
  srcDir: string;
  files: string[];
  outDir: string;
  proofsDir: string;
  leanLib: string;
  /** heartbeat budget (in thousands) of each proof obligation (vreact.json "heartbeats") */
  heartbeats?: number;
  /** In-memory source texts that replace files on disk (used by `vreact synth`, which never edits sources it checks). */
  overrides?: Map<string, string>;
  /** `vreact synth`: receives every translated `hole<T>()` with the environment (narrowing) in effect there */
  holeEnvs?: HoleEnv[];
}

/** A compiler host that reads the given files from memory instead of disk. */
export function overrideHost(options: ts.CompilerOptions, overrides: Map<string, string>): ts.CompilerHost {
  const host = ts.createCompilerHost(options);
  const norm = (f: string) => path.resolve(f);
  const texts = new Map([...overrides].map(([f, t]) => [norm(f), t]));
  const getSourceFile = host.getSourceFile.bind(host);
  host.getSourceFile = (f, lang, onError, shouldCreate) => {
    const t = texts.get(norm(f));
    return t !== undefined ? ts.createSourceFile(f, t, lang, true) : getSourceFile(f, lang, onError, shouldCreate);
  };
  const readFile = host.readFile.bind(host);
  host.readFile = (f) => texts.get(norm(f)) ?? readFile(f);
  return host;
}

export interface ModuleResult {
  tsFile: string;
  ns: string;
  defsModule: string;
  viewModule: string;
  /** Lean namespaces of the modules this one imports */
  imports: string[];
  /**
   * `obs`: ids of the obligations generated for the item (for its status); `refs`: the items
   * it uses directly (functions and constants by Lean name, components by namespace)
   */
  components: { name: string; ns: string; trusted: boolean; line: number; obs: number[]; refs: string[] }[];
  certificates: { name: string; qname: string; obs: number[]; refs: string[] }[];
  functions: { name: string; qname: string; trusted: boolean; posts: string[]; obs: number[]; refs: string[] }[];
  /** module constants; `facts`: Lean names of their module-level assert(…) theorems */
  constants: { name: string; qname: string; facts: string[]; obs: number[]; refs: string[] }[];
}

export interface TranslateResult {
  ok: boolean;
  tsDiagnostics: string[];
  errors: VtsError[];
  modules: ModuleResult[];
  obligations: Obligation[];
}

function loadProgram(cfg: Config): { program: ts.Program; diags: string[] } {
  const cfgPath = ts.findConfigFile(cfg.root, ts.sys.fileExists, "tsconfig.json");
  let options: ts.CompilerOptions = {
    strict: true,
    jsx: ts.JsxEmit.ReactJSX,
    target: ts.ScriptTarget.ES2022,
    // ES2023: toSorted / toReversed / with are part of VTS
    lib: ["lib.es2023.d.ts", "lib.dom.d.ts"],
    module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    skipLibCheck: true,
    noEmit: true,
    allowImportingTsExtensions: true,
  };
  const diags: string[] = [];
  if (cfgPath && path.dirname(cfgPath) === cfg.root) {
    const raw = ts.readConfigFile(cfgPath, ts.sys.readFile);
    const parsed = ts.parseJsonConfigFileContent(raw.config, ts.sys, path.dirname(cfgPath));
    options = { ...parsed.options, noEmit: true };
    // (an invalid tsconfig is TypeScript's error too; that its "include" matches no file does
    // not matter: the sources are vreact.json's; nor does an option this TypeScript does not know
    // (TS5023, e.g. one of a newer version): it changes nothing in this TypeScript's checks)
    const host: ts.FormatDiagnosticsHost = { getCanonicalFileName: (f) => f, getCurrentDirectory: () => cfg.root, getNewLine: () => "\n" };
    for (const d of [...(raw.error ? [raw.error] : []), ...parsed.errors]) {
      if (d.category === ts.DiagnosticCategory.Error && d.code !== 18003 && d.code !== 5023) diags.push(ts.formatDiagnostic(d, host).trim());
    }
  }
  // A bundler compiles each file on its own (Vite: esbuild, file by file), not knowing what the
  // names a file imports are: `import { Item } from "./types"; export { Item };` of a type keeps the
  // export in the JavaScript, and the module fails to load (no export named Item).  TypeScript
  // reports exactly the constructs a per-file compiler cannot compile under "isolatedModules",
  // which Vite requires: VTS always checks with it.  (TypeScript's error TS1208 for a file without
  // imports or exports is replaced by VTS's own, which says why.)
  const userIsolated = options.isolatedModules;
  options = { ...options, isolatedModules: true };
  // (strictNullChecks defaults to strict; without it TypeScript types say nothing about null and
  // undefined, which the translation reads to tell them apart)
  if (!(options.strictNullChecks ?? options.strict)) diags.push("tsconfig: VTS requires \"strict\": true, with strictNullChecks (null safety is part of the model)");
  // (without noImplicitAny an unannotated parameter is `any`: TypeScript checks nothing about it,
  // in particular not whether it is null or undefined)
  if (!(options.noImplicitAny ?? options.strict)) diags.push("tsconfig: VTS requires \"strict\": true, with noImplicitAny (TypeScript checks nothing about an implicitly-any value)");
  // the other checks of the strict family (e.g. without strictFunctionTypes a callback taking
  // `int` is accepted where one taking `int | null` is expected, and is called with null)
  for (const k of STRICT_FAMILY) {
    if (!(options[k] ?? options.strict)) diags.push(`tsconfig: VTS requires "strict": true, with ${k} (each of TypeScript's strict checks is one the translation relies on)`);
  }
  diags.push(...optionProblems(options));
  // what JSX means is configured too: VTS models React 18's automatic runtime (react/jsx-runtime)
  diags.push(...jsxConfigProblems(options));
  // a library's UMD global (`export as namespace React`) used without an import, which TypeScript
  // otherwise rejects in a module: a module bundle does not define it
  if (options.allowUmdGlobalAccess) diags.push("tsconfig: \"allowUmdGlobalAccess\" is not supported: it lets a module use a library's global (`React.useState` without importing React), which a module bundle does not define (a ReferenceError when it runs); import what you use");
  const program = ts.createProgram(cfg.files, options, cfg.overrides ? overrideHost(options, cfg.overrides) : undefined);
  const host: ts.FormatDiagnosticsHost = {
    getCanonicalFileName: (f) => f,
    getCurrentDirectory: () => cfg.root,
    getNewLine: () => "\n",
  };
  for (const f of cfg.files) {
    const sf = program.getSourceFile(f);
    if (!sf) {
      diags.push(`cannot load ${f}`);
      continue;
    }
    const rt = jsxRuntimeProblem(sf, program, cfg.root);
    if (rt) diags.push(rt);
    const ds = ts.getPreEmitDiagnostics(program, sf).filter((d) => d.category === ts.DiagnosticCategory.Error && !(d.code === 1208 && !userIsolated));
    for (const d of ds) {
      const text = ts.formatDiagnostic(d, host).trim();
      diags.push(!userIsolated && text.includes("isolatedModules") ? `${text} (VTS always checks with "isolatedModules": the bundler compiles each file on its own)` : text);
    }
  }
  return { program, diags };
}

/** TypeScript's strict checks besides strictNullChecks and noImplicitAny (each defaults to "strict"). */
const STRICT_FAMILY = ["strictFunctionTypes", "strictBindCallApply", "strictPropertyInitialization", "strictBuiltinIteratorReturn", "noImplicitThis", "useUnknownInCatchVariables", "alwaysStrict"] as const;

/**
 * The compiler options VTS accepts, as a whitelist: TypeScript keeps adding options, and some
 * switch its checks off (5.5's "noCheck" reports no type error at all), so an option VTS does not
 * know is rejected rather than trusted.  Accepted: the options the translation checks itself
 * (jsx, jsxImportSource, the strict family, the module resolution options compared with the
 * bundler's resolution), options that only add checks (noUnused*, noImplicitReturns,
 * noUncheckedIndexedAccess, exactOptionalPropertyTypes, isolatedModules, …), the language and
 * library settings (target, lib, module), options about files the program may contain (each
 * file outside node_modules must be a VTS source: checked separately), and options about emit,
 * builds and diagnostics output (VTS emits nothing).
 */
const ACCEPTED_OPTIONS = new Set<string>([
  // checked by loadProgram / the translation
  "strict", "strictNullChecks", "noImplicitAny", ...STRICT_FAMILY, "allowUmdGlobalAccess",
  // (rejected, or accepted with one value, with their own message: jsxConfigProblems)
  "jsx", "jsxImportSource", "jsxFactory", "jsxFragmentFactory", "reactNamespace",
  "paths", "baseUrl", "rootDirs", "moduleSuffixes", "customConditions", "resolvePackageJsonExports", "resolvePackageJsonImports",
  // language, library, modules
  "target", "lib", "module", "moduleResolution", "moduleDetection", "types", "typeRoots", "allowImportingTsExtensions",
  "esModuleInterop", "allowSyntheticDefaultImports", "preserveSymlinks", "resolveJsonModule", "allowArbitraryExtensions",
  "allowJs", "checkJs", "maxNodeModuleJsDepth", "useDefineForClassFields", "experimentalDecorators", "emitDecoratorMetadata",
  // more checks
  "noUnusedLocals", "noUnusedParameters", "noImplicitReturns", "noFallthroughCasesInSwitch", "noUncheckedIndexedAccess",
  "noImplicitOverride", "noPropertyAccessFromIndexSignature", "exactOptionalPropertyTypes", "noUncheckedSideEffectImports",
  "isolatedModules", "verbatimModuleSyntax", "isolatedDeclarations", "forceConsistentCasingInFileNames", "allowUnreachableCode",
  "allowUnusedLabels", "skipLibCheck", "skipDefaultLibCheck", "ignoreDeprecations",
  // emit, builds, output, editors
  "noEmit", "noEmitOnError", "noEmitHelpers", "emitDeclarationOnly", "declaration", "declarationMap", "declarationDir",
  "sourceMap", "inlineSourceMap", "inlineSources", "sourceRoot", "mapRoot", "outDir", "outFile", "rootDir", "removeComments",
  "importHelpers", "downlevelIteration", "emitBOM", "newLine", "stripInternal", "preserveConstEnums", "incremental", "composite",
  "tsBuildInfoFile", "disableSourceOfProjectReferenceRedirect", "disableSolutionSearching", "disableReferencedProjectLoad",
  "assumeChangesOnlyAffectDirectDependencies", "disableSizeLimit", "plugins", "listFiles", "listEmittedFiles", "explainFiles",
  "traceResolution", "diagnostics", "extendedDiagnostics", "generateCpuProfile", "generateTrace", "pretty", "noErrorTruncation",
  "preserveWatchOutput", "locale",
  // set by TypeScript's tsconfig parser
  "configFilePath", "pathsBasePath",
]);

/** What is wrong with the compiler options, for VTS (checked besides the strict family). */
function optionProblems(options: ts.CompilerOptions): string[] {
  const out: string[] = [];
  for (const [k, v] of Object.entries(options)) {
    if (v === undefined) continue;
    if (k === "noCheck") {
      if (v) out.push("tsconfig: \"noCheck\" is not supported: it switches TypeScript's type checking off, and VTS relies on TypeScript's checks (null and undefined, argument types, imports)");
    } else if (k === "resolvePackageJsonExports" || k === "resolvePackageJsonImports") {
      if (v === false) out.push(`tsconfig: "${k}": false is not supported: the bundler reads package.json "${k === "resolvePackageJsonExports" ? "exports" : "imports"}", so TypeScript would check another file than the one that runs`);
    } else if (!ACCEPTED_OPTIONS.has(k)) {
      out.push(`tsconfig: the compiler option "${k}" is not supported by VTS (it is not one VTS knows to leave TypeScript's checks and the meaning of the program unchanged); remove it`);
    }
  }
  return out;
}

/**
 * Compiler options that change how TypeScript resolves module specifiers but not how the bundler
 * (Vite) or Node does: TypeScript's documentation says so of "paths", "baseUrl" and "rootDirs".
 */
const TS_ONLY_RESOLUTION = ["paths", "baseUrl", "rootDirs", "moduleSuffixes", "customConditions"] as const;

/**
 * The file a library specifier (`"react"`, `"vreact/spec"`) resolves to without the TypeScript-only
 * resolution options (null: none); undefined when the program sets none of them (nothing to compare).
 */
function plainResolution(spec: string, sf: ts.SourceFile, lit: ts.StringLiteral | undefined, program: ts.Program): string | null | undefined {
  const opts = program.getCompilerOptions();
  if (!TS_ONLY_RESOLUTION.some((k) => opts[k] !== undefined)) return undefined;
  const plain: ts.CompilerOptions = { ...opts };
  for (const k of TS_ONLY_RESOLUTION) delete plain[k];
  delete plain.pathsBasePath;
  const r = ts.resolveModuleName(spec, sf.fileName, plain, ts.sys, undefined, undefined, lit ? program.getModeForUsageLocation(sf, lit) : ts.ModuleKind.ESNext);
  return r.resolvedModule?.resolvedFileName ?? null;
}

function sameFile(a: string, b: string): boolean {
  if (path.resolve(a) === path.resolve(b)) return true;
  try {
    return fs.realpathSync(a) === fs.realpathSync(b);
  } catch {
    return false;
  }
}

/** Extensions a bundler tries for a specifier without one, in order (Vite's default `resolve.extensions`). */
const BUNDLER_EXTS = [".mjs", ".js", ".mts", ".ts", ".jsx", ".tsx", ".json"];

function isFile(f: string): boolean {
  try {
    return fs.statSync(f).isFile();
  } catch {
    return false;
  }
}

/**
 * The file a bundler (Vite's default resolution) loads for the relative specifier `spec` of a
 * TypeScript file in `dir`: the path itself; a `.js`/`.jsx`/`.mjs`/`.cjs` path that does not
 * exist as its TypeScript source (`.ts`/`.tsx`, `.tsx`, `.mts`, `.cts`); the path with an
 * extension tried in order; a directory's index file (null when its package.json decides).
 */
function bundlerResolve(dir: string, spec: string): string | null {
  const p = path.resolve(dir, spec);
  if (isFile(p)) return p;
  const js = /\.(js|jsx|mjs|cjs)$/.exec(p);
  if (js) {
    const base = p.slice(0, -js[0].length);
    const exts = js[1] === "js" ? [".ts", ".tsx"] : js[1] === "jsx" ? [".tsx"] : [`.${js[1][0]}ts`];
    return exts.map((e) => base + e).find(isFile) ?? null;
  }
  const withExt = BUNDLER_EXTS.map((e) => p + e).find(isFile);
  if (withExt) return withExt;
  let dirOk = false;
  try {
    dirOk = fs.statSync(p).isDirectory();
  } catch {
    dirOk = false;
  }
  if (!dirOk || isFile(path.join(p, "package.json"))) return null;
  return BUNDLER_EXTS.map((e) => path.join(p, "index" + e)).find(isFile) ?? null;
}

/**
 * Why the import `spec` of `sf`, which TypeScript resolves to the VTS module `target`, may load
 * another file at run time (null: it cannot).  VTS modules are imported by a relative path that a
 * bundler resolves, by itself, to the file TypeScript read: tsconfig "rootDirs", "paths",
 * "baseUrl", "moduleSuffixes" and package `imports` change only TypeScript's resolution, and an
 * extensionless path is the file a bundler tries first (`./b` with both `b.js` and `b.ts` is
 * `b.js` for Vite, `b.ts` for TypeScript).
 */
function vtsImportProblem(spec: string, sf: ts.SourceFile, target: ts.SourceFile, rel: (f: string) => string): string | null {
  if (!/^\.\.?(\/|$)/.test(spec)) {
    return `VTS modules are imported by their path relative to the importing file ("./model", "../model.ts"): "${spec}" resolves to ${rel(target.fileName)} only through TypeScript's settings (tsconfig "paths"/"baseUrl", package "imports"), which the bundler does not share`;
  }
  const runtime = bundlerResolve(path.dirname(sf.fileName), spec);
  if (runtime && path.resolve(runtime) === path.resolve(target.fileName)) return null;
  let full = path.relative(path.dirname(sf.fileName), target.fileName).split(path.sep).join("/");
  if (!full.startsWith("../")) full = "./" + full;
  const own = /\.tsx?$/.test(spec) ? full : full.replace(/\.tsx?$/, "");
  const fix = runtime && path.posix.normalize(own) === path.posix.normalize(spec)
    ? `rename or remove ${rel(runtime)}, or import the file by its full name ("${full}", with tsconfig "allowImportingTsExtensions")`
    : `import it by its path relative to this file ("${own}")`;
  return `TypeScript resolves it to ${rel(target.fileName)}, but a bundler, relative to this file, ${runtime ? `loads ${rel(runtime)}` : "finds no such file"} (tsconfig "rootDirs", "paths" and "moduleSuffixes" change only what TypeScript reads, and a path without an extension is the first file a bundler finds: .mjs, .js, .mts, .ts, .jsx, .tsx, .json, then a directory's index): ${fix}`;
}

/**
 * Comments that change what a source means, to TypeScript or to the tools that compile and
 * bundle it, are rejected: the translation models the program TypeScript checked, compiled with
 * React's automatic JSX runtime, every statement kept.  Each pattern is matched anywhere in the
 * text (also in a string or JSX text: a superset of the comments the tools read) and without
 * regard to letter case, so that no spelling a tool accepts gets through:
 * - `@ts-ignore`, `@ts-expect-error` (TypeScript matches them as prefixes: `@ts-ignored`,
 *   `@ts-ignore-next-line` silence the next line too) and `@ts-nocheck` (a pragma, whose name
 *   TypeScript lower-cases: `@TS-NOCHECK` turns off the file's checks) silence TypeScript's
 *   errors, and the translation relies on TypeScript's checks (e.g. an unknown element `<bUTTON>`,
 *   a <button> once the HTML document lower-cases it);
 * - JSX pragmas (`@jsx`, `@jsxFrag`, `@jsxImportSource`, `@jsxRuntime`): TypeScript reads them,
 *   case-insensitively, from the comments at the start of the file; esbuild (Vite) and Babel from
 *   any comment.  They make JSX call another factory or library;
 * - bundler annotations (`@__PURE__`, `#__PURE__`, `@__NO_SIDE_EFFECTS__`, …): minifiers and
 *   tree-shaking delete a call so annotated whose result is unused, together with its effects
 *   (a state update).
 */
function commentDirectiveErrors(sf: ts.SourceFile, rel: string): VtsError[] {
  const errs: VtsError[] = [];
  const at = (index: number, msg: (where: string) => string) => {
    const { line, character } = sf.getLineAndCharacterOfPosition(index);
    const e = new VtsError(sf, msg(`${rel}:${line + 1}`));
    e.line = line + 1;
    e.col = character + 1;
    errs.push(e);
  };
  // (`u`: case folding, so that e.g. the Kelvin sign, which lower-cases to `k`, is a `k`)
  for (const m of sf.text.matchAll(/@ts-(ignore|expect-error|nocheck)/giu)) {
    at(m.index!, (w) => `${w}: \`${m[0]}\` is not supported: it silences TypeScript's errors, and VTS relies on TypeScript's checks (null and undefined, argument and prop types, element and attribute names, the types of library and React declarations, imports); fix the error instead`);
  }
  for (const m of sf.text.matchAll(/@jsx\w*/giu)) {
    at(m.index!, (w) => `${w}: \`${m[0]}\`: JSX pragmas (\`@jsx\`, \`@jsxImportSource\`, \`@jsxFrag\`, \`@jsxRuntime\`) are not supported: VTS models JSX as React 18's automatic runtime, and a pragma in any comment (esbuild and Babel read every comment; TypeScript the first ones, in any letter case) makes JSX call another factory or library; remove it (and do not write \`@jsx\` in a string either)`);
  }
  for (const m of sf.text.matchAll(/[@#]__[a-z_]+__/giu)) {
    at(m.index!, (w) => `${w}: the bundler annotation \`${m[0]}\` is not supported: minifiers and tree-shaking (esbuild, Rollup, Terser in a production build) delete a call annotated \`@__PURE__\` or a call of a function annotated \`@__NO_SIDE_EFFECTS__\` when its result is unused, with its effects (a state update), which VTS models as executed; remove the annotation`);
  }
  // TypeScript's own reading of the file's pragmas, in case a spelling escaped the patterns above
  const internal = sf as unknown as { pragmas?: ReadonlyMap<string, unknown>; checkJsDirective?: { enabled: boolean } };
  const own = [...(internal.pragmas?.keys() ?? [])].filter((k) => /^(jsx|ts-nocheck)/.test(k));
  if (!errs.length && (own.length || internal.checkJsDirective?.enabled === false)) {
    errs.push(new VtsError(sf, `${rel}: the comment pragma${own.length ? ` \`@${own[0]}\`` : " `@ts-nocheck`"} is not supported: it changes what TypeScript checks or what JSX means; remove it`));
  }
  return errs;
}

/**
 * What JSX means is configured: VTS models JSX as TypeScript's `react-jsx` transform, which
 * compiles `<p>…</p>` to a call of `jsx` from React 18's automatic runtime `react/jsx-runtime`
 * (or `jsxDEV` from `react/jsx-dev-runtime` under `react-jsxdev`).  Another `jsx` mode
 * (`preserve`: the bundler decides; `react`: the classic `React.createElement` factory or a
 * `jsxFactory`), another `jsxImportSource` (`preact`, a local `../rt`, whose `jsx` may do
 * anything with the element, e.g. call a button's onClick twice) would make each element mean
 * another function's result.  esbuild and Babel read these options from the tsconfig too.
 */
function jsxConfigProblems(options: ts.CompilerOptions): string[] {
  const out: string[] = [];
  if (options.jsx !== undefined && options.jsx !== ts.JsxEmit.ReactJSX && options.jsx !== ts.JsxEmit.ReactJSXDev) {
    out.push(`tsconfig: VTS requires "jsx": "react-jsx" (JSX is modelled as React 18's automatic runtime, react/jsx-runtime; "${ts.JsxEmit[options.jsx]}" makes JSX call another factory, or leaves it to the bundler)`);
  }
  if (options.jsxImportSource !== undefined && options.jsxImportSource !== "react") {
    out.push(`tsconfig: "jsxImportSource" must be "react" or absent (JSX is modelled as React 18's react/jsx-runtime; "${options.jsxImportSource}" makes every element the result of that library's jsx function)`);
  }
  for (const k of ["jsxFactory", "jsxFragmentFactory", "reactNamespace"] as const) {
    if (options[k] !== undefined) out.push(`tsconfig: the compiler option "${k}" is not supported by VTS: JSX is modelled as React 18's automatic runtime (react/jsx-runtime), not a factory; remove it`);
  }
  return out;
}

/**
 * The module the JSX of `sf` calls (`react/jsx-runtime`, or `react/jsx-dev-runtime` under
 * `react-jsxdev`; imported implicitly by the transform) must be React's, the one that runs:
 * TypeScript must resolve it into the installed react / @types/react package, and to the same
 * file without the TypeScript-only resolution options ("paths", "baseUrl", "rootDirs", …, which
 * could map it to a file of the project or to another library: the bundler loads React's).
 * (TypeScript reports a missing runtime itself.)
 */
function jsxRuntimeProblem(sf: ts.SourceFile, program: ts.Program, root: string): string | null {
  if (sf.languageVariant !== ts.LanguageVariant.JSX) return null;
  const options = program.getCompilerOptions();
  const spec = `react/${options.jsx === ts.JsxEmit.ReactJSXDev ? "jsx-dev-runtime" : "jsx-runtime"}`;
  const full = ts.resolveModuleName(spec, sf.fileName, options, ts.sys, undefined, undefined, ts.ModuleKind.ESNext).resolvedModule?.resolvedFileName;
  const plain = plainResolution(spec, sf, undefined, program);
  let real = full;
  try {
    if (full) real = fs.realpathSync(full);
  } catch {
    // keep the resolved name
  }
  const notReact = !!real && !/[\\/]node_modules[\\/](@types[\\/])?react[\\/][^\\/]+$/.test(real);
  const differs = plain !== undefined && (!full || !plain || !sameFile(full, plain));
  if (!notReact && !differs) return null;
  const rel = (f: string) => path.relative(root, f);
  const how = differs ? ` (through tsconfig "paths"/"baseUrl"/"rootDirs"; without them, as the bundler resolves it: ${plain ? rel(plain) : "nothing"})` : ` (tsconfig "paths" or another setting redirects it)`;
  return `${rel(sf.fileName)}: its JSX imports "${spec}", which TypeScript resolves to ${real ? rel(real) : "nothing"}${notReact ? ", not to React's" : ""}${how}: VTS models JSX as React 18's automatic runtime, the one the bundler loads; remove the mapping`;
}

/** The Lean namespace of the module of source file `f` (also used by `vreact synth`, whose type names must match). */
export function moduleNs(srcDir: string, f: string): string {
  const rel = path.relative(srcDir, f).replace(/\.(tsx?|jsx?)$/, "");
  return "VTS." + rel.split(path.sep).map(sanitizeSeg).join(".");
}

/** A module path segment as a Lean namespace / module name component (also a directory name). */
function sanitizeSeg(s: string): string {
  const t0 = s.replace(/[^A-Za-z0-9_]/g, "_");
  const t = /^[A-Za-z_]/.test(t0) ? t0 : "M" + t0;
  // a Lean token (`end`, `at`, `Type`) does not parse as a name component, and a Lean or
  // generated name (`List`, `VReact`) would capture references (`List.map` inside VTS.List)
  return clashesWithLean(t) ? t + "_" : t;
}

/** Is the type annotation React's node type (`JSX.Element`, `ReactNode`, `ReactElement`, also `… | null`), by its declaration? */
function isReactNodeType(t: ts.TypeNode, prog: Program): boolean {
  if (ts.isParenthesizedTypeNode(t)) return isReactNodeType(t.type, prog);
  if (ts.isUnionTypeNode(t)) return t.types.some((x) => isReactNodeType(x, prog));
  return ts.isTypeReferenceNode(t) && !!prog.typeEnv.isReactType(t, ["ReactNode", "ReactElement", "Element"]);
}

/** A component: a capitalised function returning React's node type or containing JSX (also used by `vreact synth`). */
export function isComponentDecl(fn: ts.FunctionDeclaration, prog: Program): boolean {
  const name = fn.name?.text ?? "";
  if (!/^[A-Z]/.test(name)) return false;
  if (fn.type && isReactNodeType(fn.type, prog)) return true;
  let jsx = false;
  const visit = (n: ts.Node) => {
    if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n)) jsx = true;
    if (!jsx) ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return jsx;
}

function isTrusted(n: ts.Node): boolean {
  return ts.getJSDocTags(n).some((t) => t.tagName.text === "trusted");
}
function isOpaque(n: ts.Node): boolean {
  return ts.getJSDocTags(n).some((t) => t.tagName.text === "opaque");
}

export function translate(cfg: Config): TranslateResult {
  const res = translateAll(cfg);
  // (one problem reached twice — a type alias checked where it is declared and again where it is
  // used — is reported once)
  const seen = new Set<string>();
  res.errors = res.errors.filter((e) => {
    const key = `${e.file}:${e.line}:${e.col}:${e.message}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
  return res;
}

function translateAll(cfg: Config): TranslateResult {
  const { program, diags } = loadProgram(cfg);
  const res: TranslateResult = { ok: false, tsDiagnostics: diags, errors: [], modules: [], obligations: [] };
  if (diags.length) return res;
  const checker = program.getTypeChecker();
  const fileSet = new Set(cfg.files.map((f) => path.resolve(f)));
  const nsOfFile = (f: string) => moduleNs(cfg.srcDir, f);
  const sfs = cfg.files.map((f) => program.getSourceFile(f)!);
  const prog = new Program(program, cfg.root, (sf) => nsOfFile(sf.fileName), sfs);
  prog.holeEnvs = cfg.holeEnvs;

  // ---- the types of the program come from TypeScript's and external libraries (node_modules:
  // React, vreact/spec) and from the VTS sources, nothing else: a declaration file of the project
  // (`/// <reference path>`, tsconfig "typeRoots"/"types"/"paths") or a script file's global
  // declarations could change the types of library declarations (`declare global`, interface
  // merging with `Array`/`Math`/`String`, ambient `declare const`) that the translation relies
  // on, without being checked ----
  for (const f of program.getSourceFiles()) {
    if (prog.isLibraryFile(f) || fileSet.has(path.resolve(f.fileName))) continue;
    res.errors.push(new VtsError(f, `${path.relative(cfg.root, f.fileName)} is part of the TypeScript program (through a \`/// <reference>\`, an import or the tsconfig) but is not a VTS source: declarations outside the verified program (\`declare global\`, ambient declarations, interfaces merged with library types) could change what library code means, unchecked; remove it from the program`));
  }
  for (const sf of sfs) {
    const rel = path.relative(cfg.root, sf.fileName);
    if (!ts.isExternalModule(sf)) {
      res.errors.push(new VtsError(sf, `${rel} is not a module (it has no import or export): TypeScript makes the declarations of such a file global, and merges its interfaces with the libraries' (\`interface Math { … }\`); add an import or an export`));
    }
    res.errors.push(...commentDirectiveErrors(sf, rel));
    // the bundler compiles a file with the settings of the tsconfig.json nearest to it (Vite's
    // esbuild reads its jsx, jsxImportSource, verbatimModuleSyntax, …); VTS checks every source
    // with the project's: a tsconfig.json in a source directory could make JSX another library's,
    // or keep an import of a type
    const nearest = ts.findConfigFile(path.dirname(sf.fileName), ts.sys.fileExists, "tsconfig.json");
    if (nearest && path.dirname(path.resolve(nearest)) !== path.resolve(cfg.root) && !path.relative(cfg.root, nearest).startsWith("..")) {
      res.errors.push(new VtsError(sf, `${rel}: ${path.relative(cfg.root, nearest)} is not supported: the bundler compiles ${rel} with the settings of the tsconfig.json nearest to it, but VTS checks it with the project's tsconfig.json; put the settings in the project's tsconfig.json and remove ${path.relative(cfg.root, nearest)}`));
    }

    // (`/// <reference path>` to anything but a VTS source is rejected above; `lib` and `types`
    // references add TypeScript's and installed libraries)
    if (sf.hasNoDefaultLib) {
      res.errors.push(new VtsError(sf, `${rel}: \`/// <reference no-default-lib="true"/>\` is not supported (the program's JavaScript globals must be TypeScript's standard library)`));
    }
  }
  if (res.errors.length) return res;
  const counter = { n: 0 };

  // ---- one Lean module per source file: two files whose names map to the same Lean
  // namespace (e.g. limits.ts / limits.tsx, my-limits.ts / my_limits.ts), or to output
  // paths that differ only in case (todo.ts / Todo.tsx on a case-insensitive disk), would
  // overwrite each other's generated Lean ----
  const byNs = new Map<string, ts.SourceFile>();
  for (const sf of sfs) {
    const ns = nsOfFile(sf.fileName);
    const other = byNs.get(ns.toLowerCase());
    if (!other) {
      byNs.set(ns.toLowerCase(), sf);
      continue;
    }
    const a = path.relative(cfg.root, other.fileName), b = path.relative(cfg.root, sf.fileName);
    const otherNs = nsOfFile(other.fileName);
    const same = otherNs === ns ? `the same Lean module ${ns}` : `Lean modules ${otherNs} and ${ns}, whose files differ only in letter case`;
    res.errors.push(new VtsError(sf, `module name clash: ${a} and ${b} translate to ${same} (a module is named after its path without the .ts/.tsx extension, other characters than letters, digits and _ become _, and a segment that is a Lean keyword or Lean name gets a trailing _); rename one of the files`));
  }
  if (res.errors.length) return res;
  // ---- a module's generated files go to the directory VTS/<segments>/: two modules whose
  // directories differ only in letter case (src/lib.ts → VTS/lib/, src/Lib/x.ts → VTS/Lib/x/)
  // would share one directory on a case-insensitive disk, where Lean's messages name a path
  // that is not the one on disk ----
  const dirs = new Map<string, { dir: string; sf: ts.SourceFile }>();
  for (const sf of sfs) {
    const segs = nsOfFile(sf.fileName).split(".");
    for (let k = 2; k <= segs.length; k++) {
      const dir = segs.slice(0, k).join("/");
      const other = dirs.get(dir.toLowerCase());
      if (!other) {
        dirs.set(dir.toLowerCase(), { dir, sf });
        continue;
      }
      if (other.dir === dir) continue;
      const a = path.relative(cfg.root, other.sf.fileName), b = path.relative(cfg.root, sf.fileName);
      res.errors.push(new VtsError(sf, `module path clash: ${a} and ${b} put their generated Lean into the directories ${other.dir}/ and ${dir}/, which differ only in letter case (one directory on a case-insensitive disk); rename one of them so that the names (here \`${other.dir.split("/").pop()}\` and \`${dir.split("/").pop()}\`) are spelled the same or differ by more than case`));
      break;
    }
  }
  if (res.errors.length) return res;

  // ---- import graph & topological order ----
  // (TypeScript resolves a specifier with settings the bundler does not share — tsconfig "paths",
  // "baseUrl", "rootDirs", "moduleSuffixes" — so every import must name, by itself, the file
  // TypeScript read: React and vreact/spec are the installed packages, VTS modules are relative
  // paths that a bundler resolves to the same file)
  const importsOf = new Map<ts.SourceFile, ts.SourceFile[]>();
  for (const sf of sfs) {
    const deps: ts.SourceFile[] = [];
    for (const st of sf.statements) {
      // imports, and re-exports (`export … from "./m"`), which load (evaluate) their module too
      if (!ts.isImportDeclaration(st) && !(ts.isExportDeclaration(st) && st.moduleSpecifier)) continue;
      const spec = (st.moduleSpecifier as ts.StringLiteral).text;
      const target = moduleFile(checker, st.moduleSpecifier!);
      const what = `${ts.isImportDeclaration(st) ? "import" : "re-export"} of "${spec}"`;
      const rel = (f: string) => (path.resolve(f).startsWith(cfg.root + path.sep) ? path.relative(cfg.root, f) : f);
      // React and vreact/spec: by the declaration file the specifier resolves to, which must be
      // the installed package's (never a project file), also without TypeScript-only settings
      if (spec === "react" || spec === "react/jsx-runtime" || spec === SPEC_MODULE) {
        const lib = spec === SPEC_MODULE ? "vreact/spec" : "React";
        const isLib = (f: ts.SourceFile) => (spec === SPEC_MODULE ? prog.specFiles.has(f) : prog.isReactFile(f));
        if (!target || !isLib(target)) {
          res.errors.push(new VtsError(st, `${what}: it resolves to ${target ? rel(target.fileName) : "no declaration file"}, not to the installed ${lib} package's declarations, which are what runs (the bundler loads the package; tsconfig "paths"/"baseUrl" change only what TypeScript reads)`));
        } else {
          const plain = plainResolution(spec, sf, st.moduleSpecifier as ts.StringLiteral, program);
          if (plain !== undefined && (!plain || !sameFile(plain, target.fileName))) {
            res.errors.push(new VtsError(st, `${what}: TypeScript resolves it to ${rel(target.fileName)} only through tsconfig "paths"/"baseUrl" (without them: ${plain ? rel(plain) : "nothing"}), which the bundler does not use; remove the mapping`));
          }
        }
        continue;
      }
      if (target && fileSet.has(path.resolve(target.fileName))) {
        const problem = vtsImportProblem(spec, sf, target, rel);
        if (problem) res.errors.push(new VtsError(st, `${what}: ${problem}`));
        deps.push(target);
        continue;
      }
      res.errors.push(new VtsError(st, `${what} is outside the verified program (only react, vreact/spec, and other VTS modules may be imported)`));
    }
    // (the implicit import of React's "react/jsx-runtime" by JSX: the same rule, jsxRuntimeProblem)
    importsOf.set(sf, deps);
  }
  const order: ts.SourceFile[] = [];
  const state = new Map<ts.SourceFile, number>();
  const visit = (sf: ts.SourceFile, stack: ts.SourceFile[]) => {
    const st = state.get(sf);
    if (st === 2) return;
    if (st === 1) {
      res.errors.push(new VtsError(sf.statements[0], `import cycle: ${[...stack, sf].map((s) => path.basename(s.fileName)).join(" → ")}`));
      return;
    }
    state.set(sf, 1);
    for (const d of importsOf.get(sf) ?? []) visit(d, [...stack, sf]);
    state.set(sf, 2);
    order.push(sf);
  };
  for (const sf of sfs) visit(sf, []);
  if (res.errors.length) return res;

  // ---- declaration prepass ----
  const mods = new Map<ts.SourceFile, ModCtx>();
  for (const sf of order) {
    const ns = nsOfFile(sf.fileName);
    const m = new ModCtx(prog, ns, sf, res.obligations, counter);
    mods.set(sf, m);
    for (const st of sf.statements) {
      try {
        collect(st, m, ns, res);
      } catch (e) {
        if (e instanceof VtsError) res.errors.push(e);
        else throw e;
      }
    }
  }
  if (res.errors.length) return res;
  // ---- module initialisation order (temporal dead zone) ----
  for (const sf of order) {
    try {
      checkInitOrder(sf, mods.get(sf)!);
    } catch (e) {
      if (e instanceof VtsError) res.errors.push(e);
      else throw e;
    }
  }
  if (res.errors.length) return res;

  // ---- translation ----
  fs.mkdirSync(cfg.outDir, { recursive: true });
  const leanFiles: { rel: string; text: string }[] = [];
  const proofModules = new Set<string>();
  // copy user proofs
  if (fs.existsSync(cfg.proofsDir)) {
    const walk = (d: string) => {
      for (const f of fs.readdirSync(d)) {
        const p = path.join(d, f);
        if (fs.statSync(p).isDirectory()) walk(p);
        else if (f.endsWith(".lean")) {
          const rel = path.relative(cfg.proofsDir, p);
          leanFiles.push({ rel: path.join("Proofs", rel), text: fs.readFileSync(p, "utf8") });
          proofModules.add("Proofs." + rel.replace(/\.lean$/, "").split(path.sep).join("."));
        }
      }
    };
    walk(cfg.proofsDir);
  }
  // user proofs are imported by the generated files, so what they declare takes effect while
  // the translation is checked: only lemma-like commands may pass (lean/ProofCheck.lean)
  const proofIssues = checkProofFiles(
    cfg.leanLib,
    leanFiles.map((f) => ({ name: path.relative("Proofs", f.rel).split(path.sep).join("/"), text: f.text })),
  );
  for (const i of proofIssues) {
    const e = new VtsError(undefined, i.msg);
    e.file = path.join(cfg.proofsDir, ...i.file.split("/"));
    e.line = i.line;
    e.col = i.col;
    res.errors.push(e);
  }
  if (res.errors.length) return res;
  /** the Lean names each module generates, for `nameClashes` */
  const declared = new Map<ts.SourceFile, GeneratedNames>();
  // the user lemmas about a module's functions (proofs/<Up>.lean) are imported into the Defs of
  // every module importing it, so they help those modules' function bodies and contracts too
  const upProofs = upstreamProofs(
    order.map((sf) => ({ ns: nsOfFile(sf.fileName), deps: (importsOf.get(sf) ?? []).map((d) => nsOfFile(d.fileName)) })),
    new Map(leanFiles.map((f) => ["Proofs." + f.rel.replace(/\.lean$/, "").split(path.sep).slice(1).join("."), f.text])),
  );
  // A module with a `proofs/<Mod>.lean` puts the postconditions of the functions that nothing
  // else in its Defs uses into Posts.lean, after those lemmas (which import Defs), so that the
  // lemmas help them; everything that may use such a postcondition imports Posts: the module's
  // View and the Defs of the modules importing it. Only when every importing module can import
  // `Proofs.<Mod>` (no import cycle through the lemma file); otherwise all postconditions stay in
  // Defs, where importing modules see them.
  const proofOfNs = (ns: string) => "Proofs." + ns.split(".").slice(1).join(".");
  const importersOf = new Map<string, string[]>();
  for (const sf of order) for (const d of importsOf.get(sf) ?? []) importersOf.set(nsOfFile(d.fileName), [...(importersOf.get(nsOfFile(d.fileName)) ?? []), nsOfFile(sf.fileName)]);
  const canDefer = (ns: string) => proofModules.has(proofOfNs(ns)) && (importersOf.get(ns) ?? []).every((b) => (upProofs.get(b) ?? []).includes(proofOfNs(ns)));
  /** the modules that have a Posts.lean (modules come dependencies first) */
  const withPostsFile = new Set<string>();
  for (const sf of order) {
    const m = mods.get(sf)!;
    const ns = m.ns;
    const modRes: ModuleResult = { tsFile: sf.fileName, ns, defsModule: `${ns}.Defs`, viewModule: `${ns}.View`, imports: (importsOf.get(sf) ?? []).map((d) => nsOfFile(d.fileName)), components: [], functions: [], certificates: [], constants: [] };
    // ids of the obligations generated by `f()`
    const obsOf = <R>(f: () => R): { r: R; obs: number[] } => {
      const from = counter.n;
      const r = f();
      return { r, obs: Array.from({ length: counter.n - from }, (_, k) => from + k + 1) };
    };
    const deps = (importsOf.get(sf) ?? []).map((d) => nsOfFile(d.fileName));
    const rel = ns.split(".").join(path.sep);
    const proofMod = "Proofs." + ns.split(".").slice(1).join(".");
    const withPosts = canDefer(ns);
    let defs = header([...deps.map((d) => `${d}.Defs`), ...(proofModules.has("Proofs.Base") ? ["Proofs.Base"] : []), ...(upProofs.get(ns) ?? []), ...deps.filter((d) => withPostsFile.has(d)).map((d) => `${d}.Posts`)]) + `namespace ${ns}\n\n`;
    // (the headers of View.lean and Posts.lean are added at the end: View imports Posts if there is one)
    let view = `namespace ${ns}\n\n`;
    let posts = `namespace ${ns}\n\n`;
    /** functions whose postconditions are in Posts.lean */
    const deferred = new Set<string>();
    // the types of this module go here, emitted once the module is translated: inline types
    // first met in bodies (local annotations, `hole<{ … }>()`, `useState<"a" | "b">`) are
    // registered during the translation (in registration order: a type after the ones it uses)
    const typesAt = defs.length;
    try {
      // constants & functions, dependency-ordered; each function's postconditions right
      // after it, so that the bodies of later functions (in this module and in importing
      // modules' Defs) can use them through `vreact_contracts`
      const decls = sortDecls(sf, m);
      const usedInDefs = withPosts ? usedByOthers(decls, m) : new Set<ts.Node>();
      // the facts (module-level asserts) about constants, each emitted as soon as everything
      // it mentions is (right after its constant, unless it calls a function declared later)
      const declSet = new Set(decls);
      const emitted = new Set<ts.Node>();
      const pendingFacts: { d: ts.VariableDeclaration; info: ConstInfo; k: number; deps: ts.Node[] }[] = [];
      for (const d of decls) {
        const g = prog.globals.get(d)!;
        if (g.k === "const") g.info.facts.forEach((f, k) => pendingFacts.push({ d: d as ts.VariableDeclaration, info: g.info, k, deps: factDeps(f, declSet, m) }));
      }
      const flushFacts = () => {
        for (let i = 0; i < pendingFacts.length; ) {
          const p = pendingFacts[i];
          if (!p.deps.every((x) => emitted.has(x)) || !emitted.has(p.d)) {
            i++;
            continue;
          }
          pendingFacts.splice(i, 1);
          const { r, obs } = obsOf(() => translateFact(p.d, p.info, p.k, m));
          defs += r + "\n";
          modRes.constants.find((c) => c.qname === p.info.qname)!.obs.push(...obs);
        }
      };
      for (const d of decls) {
        const g = prog.globals.get(d)!;
        if (g.k === "const") {
          const { r, obs } = obsOf(() => translateConst(d as ts.VariableDeclaration, g.info, m));
          defs += r + "\n";
          // (g.info.qname is already escaped: `max'`, `«$x»`)
          const facts = g.info.facts.map((_, k) => `${g.info.qname}.${k === 0 ? "post" : `post${k + 1}`}`);
          modRes.constants.push({ name: ((d as ts.VariableDeclaration).name as ts.Identifier).text, qname: g.info.qname, facts, obs, refs: itemRefs([d, ...g.info.facts], d, m) });
        }
        if (g.k === "fn") {
          const { r, obs } = obsOf(() => translateFunction(d as ts.FunctionDeclaration, g.info, m));
          defs += r.def + "\n";
          if (r.post && withPosts && !usedInDefs.has(d)) {
            posts += r.post + "\n";
            deferred.add(g.info.qname);
          } else if (r.post) defs += r.post + "\n";
          modRes.functions.push({ name: g.info.name, qname: `${ns}.${leanIdent(g.info.name)}`, trusted: g.info.trusted, posts: r.postNames, obs, refs: itemRefs([d], d, m) });
        }
        emitted.add(d);
        flushFacts();
      }
      if (pendingFacts.length) throw new Error(`facts left unemitted: ${pendingFacts.map((p) => p.info.qname).join(", ")}`);
      // components, children first
      for (const c of sortComponents(sf, m)) {
        const g = prog.globals.get(c) as { k: "comp"; info: CompInfo };
        const { r, obs } = obsOf(() => translateComponent(c as ts.FunctionDeclaration, g.info, m));
        view += r + "\n";
        const { line } = sf.getLineAndCharacterOfPosition(c.getStart(sf));
        modRes.components.push({ name: g.info.name, ns: g.info.ns, trusted: g.info.trusted, line: line + 1, obs, refs: itemRefs([c], c, m) });
      }
      // application roots (no props): element + whole-app soundness certificate
      for (const c of sortComponents(sf, m)) {
        const g = prog.globals.get(c) as { k: "comp"; info: CompInfo };
        const info = g.info;
        if (info.data.length || info.callbacks.length) continue;
        const N = info.ns;
        const L = leanIdent(info.name); // the component's namespace in this module (as in N)
        view += `/-- \`<${info.name}/>\` as the root element of an application. -/\n`;
        const rootOb = obsOf(() => m.ob(c, "root-precondition", `<${info.name}/> can be mounted as the application root`));
        view += `theorem ${L}.root_pre : ${N}.pre ${N}.Props.mk :=\n  ${rootOb.r}\n\n`;
        view += `noncomputable def ${L}.element : VReact.CompNode Empty :=\n  ⟨${N}.spec, ${N}.Props.mk, ${N}.Cb.mk, ${N}.root_pre,\n   fun s h => ${N}.component.render ${N}.Props.mk ${N}.Cb.mk s ${N}.root_pre h⟩\n\n`;
        view += `/-- **Certificate.** In every run of the application rooted at \`<${info.name}/>\` — any sequence of\nuser events, effect flushes and timer callbacks — every mounted component instance satisfies\nits invariant (instantiation of \`VReact.run_allInv\`). -/\n`;
        view += `theorem ${L}.certificate (fuel : Nat) (acts : List VReact.Action) :\n    (VReact.run fuel ${N}.element acts).AllInv :=\n  VReact.run_allInv fuel ${N}.element acts\n\n`;
        const compObs = modRes.components.find((x) => x.ns === N)?.obs ?? [];
        modRes.certificates.push({ name: info.name, qname: `${N}.certificate`, obs: [...compObs, ...rootOb.obs], refs: [N] });
      }
      // (axiom reports are printed after the namespace is closed, with full names)
    } catch (e) {
      if (e instanceof VtsError) {
        res.errors.push(e);
        continue;
      }
      throw e;
    }
    let types = "";
    for (const nt of prog.reg.order) {
      if (nt.module !== ns) continue;
      // props types with callbacks are represented by the component's Props/Cb structures; a
      // type with a function or React node anywhere has no Lean value type (every use of it as
      // data is rejected: checkValueType)
      if ((nt.def.k === "rec" || nt.def.k === "union") && nonValuePart({ k: nt.def.k, name: nt.qname }, prog.reg)) continue;
      types += emitTypeDecl(nt, prog.reg) + "\n";
    }
    defs = defs.slice(0, typesAt) + types + defs.slice(typesAt);
    // every declaration's axioms are reported, in the file that declares it (so a failure in
    // a function body still leaves the other functions of the module with a real status)
    defs += `\nend ${ns}\n\n`;
    for (const c of modRes.constants) for (const q of [c.qname, ...c.facts]) defs += axiomReport(q);
    for (const f of modRes.functions) for (const q of [f.qname, ...(deferred.has(f.qname) ? [] : f.posts)]) defs += axiomReport(q);
    defs += `#eval "vreact:checked"\n`;
    if (deferred.size) {
      withPostsFile.add(ns);
      posts += `\nend ${ns}\n\n`;
      for (const f of modRes.functions) if (deferred.has(f.qname)) for (const q of f.posts) posts += axiomReport(q);
      posts = header([`${ns}.Defs`, proofMod]) + posts + `#eval "vreact:checked"\n`;
    } else posts = "";
    view = header([deferred.size ? `${ns}.Posts` : `${ns}.Defs`, ...deps.map((d) => `${d}.View`), ...(proofModules.has(proofMod) ? [proofMod] : [])]) + view;
    view += `\nend ${ns}\n\n`;
    for (const c of modRes.components) view += axiomReport(`${c.ns}.component`);
    for (const c of modRes.certificates) view += axiomReport(c.qname);
    view += `#eval "vreact:checked"\n`;
    leanFiles.push({ rel: path.join(rel, "Defs.lean"), text: withBudget(defs, cfg.heartbeats) });
    if (posts) leanFiles.push({ rel: path.join(rel, "Posts.lean"), text: withBudget(posts, cfg.heartbeats) });
    leanFiles.push({ rel: path.join(rel, "View.lean"), text: withBudget(view, cfg.heartbeats) });
    declared.set(sf, generatedNames(defs + "\n" + posts + "\n" + view));
    res.modules.push(modRes);
  }
  if (res.errors.length) return res;
  nameClashes(order, declared, nsOfFile, cfg.root, res);
  if (res.errors.length) return res;
  // root module and lake project
  const rootImports = res.modules.map((mr) => `import ${mr.viewModule}`).join("\n");
  leanFiles.push({ rel: "VTS.lean", text: rootImports + "\n" });
  const libs = [`[[lean_lib]]\nname = "VTS"\n`];
  if (proofModules.size) libs.push(`[[lean_lib]]\nname = "Proofs"\n`);
  // (no shared artifact cache: every module is built here, by a Lean run vreact starts — see
  // `runLake` — never taken from a cache another project or machine can write)
  const lakefile = `name = "vts"\ndefaultTargets = ["VTS"]\nenableArtifactCache = false\n\n[[require]]\nname = "VReact"\npath = ${JSON.stringify(cfg.leanLib)}\n\n${libs.join("\n")}`;
  leanFiles.push({ rel: "lakefile.toml", text: lakefile });
  leanFiles.push({ rel: "lean-toolchain", text: fs.readFileSync(path.join(cfg.leanLib, "lean-toolchain"), "utf8") });
  // backstop: no two generated files may share a path (also on case-insensitive disks)
  const paths = new Map<string, string>();
  for (const f of leanFiles) {
    const prev = paths.get(f.rel.toLowerCase());
    if (prev !== undefined) res.errors.push(new VtsError(undefined, `generated Lean files ${prev} and ${f.rel} would overwrite each other (rename one of the source or proof files)`));
    paths.set(f.rel.toLowerCase(), f.rel);
  }
  if (res.errors.length) return res;
  // write, removing stale generated files
  fs.rmSync(path.join(cfg.outDir, "VTS"), { recursive: true, force: true });
  fs.rmSync(path.join(cfg.outDir, "Proofs"), { recursive: true, force: true });
  for (const f of leanFiles) {
    const p = path.join(cfg.outDir, f.rel);
    fs.mkdirSync(path.dirname(p), { recursive: true });
    if (!fs.existsSync(p) || fs.readFileSync(p, "utf8") !== f.text) fs.writeFileSync(p, f.text);
  }
  // a manifest written for another location of the library (a project copied or moved with its
  // `.vreact/`) still names that VReact: lake would keep building against it, so it is removed
  // and lake writes a new one from the lakefile
  const manifest = path.join(cfg.outDir, "lake-manifest.json");
  if (fs.existsSync(manifest) && !manifestMatches(manifest, { VReact: cfg.leanLib })) fs.rmSync(manifest, { force: true });
  res.ok = true;
  return res;
}

/**
 * The axiom report of a reported declaration: `#print axioms` (Lean's own), and
 * `#vreact_assumed` (VReact/Assumed.lean), which names the declarations outside the generated
 * code that use `VReact.assumed` — the axiom behind `assume(…)` — in its cone: the report
 * counts `VReact.assumed` as the program's `assume(…)` facts only where that list is empty.
 */
function axiomReport(q: string): string {
  return `#print axioms ${q}\n#vreact_assumed ${q}\n`;
}

/** The Lean names a module's generated files declare (see `nameClashes`). */
interface GeneratedNames {
  /** declarations, and the names Lean derives from a structure/inductive (its fields,
   * constructors, recursors, …) */
  names: string[];
  /** definitions and theorems: Lean (equation lemmas, `match`/proof auxiliaries) and vreact
   * (the contracts `f.post`, `f.post2`, … of a function `f`) look up names below them */
  defs: string[];
  /** the generated code without comments and string literals (for the identifiers it uses
   * unqualified) */
  code: string;
}

function generatedNames(text: string): GeneratedNames {
  const lines = text.split("\n");
  const names: string[] = [];
  const defs: string[] = [];
  for (const d of leanDecls(text)) {
    if (!d.name) continue;
    names.push(d.name);
    if (d.kind === "structure" || d.kind === "inductive" || d.kind === "class") {
      for (const aux of LEAN_TYPE_AUX) names.push(`${d.name}.${aux}`);
      // the generator writes one field (`  x : T`) or constructor (`  | c …`) per line
      for (const l of lines.slice(d.start, d.end)) {
        const m = /^  (?:\| )?(«[^»]*»|[^\s:(|{]+)/.exec(l);
        if (m && !m[1].startsWith("/-") && !m[1].startsWith("--")) names.push(`${d.name}.${m[1]}`);
      }
    } else if (["def", "abbrev", "opaque", "theorem", "instance"].includes(d.kind)) defs.push(d.name);
  }
  const code = text.replace(/\/-[\s\S]*?-\//g, " ").replace(/--[^\n]*/g, " ").replace(/"(?:[^"\\]|\\.)*"/g, '""');
  return { names, defs, code };
}

const ROOT_NAME = new Set(LEAN_ROOT_NAMES);
/** Names below a definition `f` that Lean generates on its own or vreact looks up by name. */
const DEF_AUX = /^(?:post\d*|eq_\d+|eq_def|eq_unfold|match_\d+|proof_\d+|induct\w*|fun_cases\w*|mutual_induct\w*|_.*)$/;

/**
 * Two modules must not generate the same Lean name: `src/a.ts` declaring `b` (`VTS.a.b`, with
 * `VTS.a.b.post` for its ensures) and a module `src/a/b.ts` (namespace `VTS.a.b`) declaring
 * `post` (`VTS.a.b.post` too) cannot both be imported by one Lean module. Below another
 * module's definition `f`, a module also may not declare a name Lean derives from `f` (an
 * equation lemma `f.eq_1`, …) or that vreact looks up as `f`'s contract (`f.post`, `f.post2`,
 * …), even when `f` has none. Namespaces may otherwise nest: a component `Board` of
 * `src/ui.tsx` (`VTS.ui.Board.Props`, …) next to a module `src/ui/Board.tsx` (its component
 * `Cell` is `VTS.ui.Board.Cell.Props`, …) is fine, unless a member of the enclosing declaration
 * (a field `max` of a type `range`, say: `VTS.model.range.max`) is a root-level Lean name that
 * the nested module's generated code uses unqualified: Lean would find the member instead.
 * (The names Lean derives on its own outside a declaration's namespace, such as `deriving`
 * instances, are not covered; such a clash is a Lean build error.)
 */
function nameClashes(order: ts.SourceFile[], declared: Map<ts.SourceFile, GeneratedNames>, nsOfFile: (f: string) => string, root: string, res: TranslateResult) {
  const owners = new Map<string, ts.SourceFile[]>();
  const defOwner = new Map<string, ts.SourceFile>();
  for (const sf of order) {
    for (const n of new Set(declared.get(sf)?.names ?? [])) owners.set(n, [...(owners.get(n) ?? []), sf]);
    for (const n of declared.get(sf)?.defs ?? []) if (!defOwner.has(n)) defOwner.set(n, sf);
  }
  const rel = (sf: ts.SourceFile) => path.relative(root, sf.fileName);
  /** `inner`'s namespace lies inside `outer`'s declaration that `name` is (or is below) */
  const clash = (inner: ts.SourceFile, outer: ts.SourceFile, name: string, why: string) => {
    const nsO = nsOfFile(outer.fileName);
    const nsI = nsOfFile(inner.fileName);
    const tsName = name.slice(nsO.length + 1).split(".")[0].replace(/^«|»$/g, "").replace(/'$/, "");
    res.errors.push(new VtsError(inner.statements[0] ?? inner,
      `Lean name clash: the module ${rel(inner)} has the Lean namespace ${nsI}, which ${rel(outer)} already uses for its declaration \`${tsName}\` (${why}); rename the file (or its directory) or the declaration \`${tsName}\``));
  };
  for (const sf of order) {
    const ns = nsOfFile(sf.fileName);
    const g = declared.get(sf);
    if (!g) continue;
    // an exact clash is reported for the module whose namespace is longer: it lies inside the
    // other module's declaration
    const exact = g.names.map((n) => ({ n, o: (owners.get(n) ?? []).find((o) => o !== sf && nsOfFile(o.fileName).length < ns.length) })).find((c) => c.o);
    if (exact) {
      clash(sf, exact.o!, exact.n, `both generate the Lean name ${exact.n}`);
      continue;
    }
    let found = false;
    // members of another module's declarations in the namespaces this module's code is in
    const segsNs = ns.split(".");
    for (let k = 2; k <= segsNs.length && !found; k++) {
      const p = segsNs.slice(0, k).join(".");
      for (const [n, os] of owners) {
        if (!n.startsWith(p + ".") || n.slice(p.length + 1).includes(".")) continue;
        const x = n.slice(p.length + 1);
        const o = os.find((o) => o !== sf);
        // (a field name in `{ x := … }` or a declaration `x : T` is not a use)
        if (!o || !ROOT_NAME.has(x) || !new RegExp(`(?<![\\w.'«])${x.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w'])(?!\\s*:)`).test(g.code)) continue;
        clash(sf, o, n, `whose member ${n} Lean would find instead of its own \`${x}\` in the code of ${rel(sf)}`);
        found = true;
        break;
      }
    }
    if (found) continue;
    for (const n of g.names) {
      if (!n.startsWith(ns + ".")) continue;
      const segs = n.split(".");
      for (let k = ns.split(".").length; k < segs.length; k++) {
        const q = segs.slice(0, k).join(".");
        const o = defOwner.get(q);
        if (!o || o === sf || !DEF_AUX.test(segs[k])) continue;
        clash(sf, o, q, `Lean and vreact derive names such as ${q}.${segs[k]} from it: its equation lemmas, its contracts \`.post\`, \`.post2\`, …`);
        found = true;
        break;
      }
      if (found) break;
    }
  }
}

/** Heartbeats (in thousands) of each proof obligation (`vreact_ob`, see VReact/Budget.lean). */
const OB_HEARTBEATS = 1000000;
/** Heartbeats (in thousands) for a declaration's own elaboration and kernel check. */
const DECL_HEARTBEATS = 1000000;
const BUDGET_SLOT = "set_option maxHeartbeats @BUDGET@";

/**
 * Every obligation runs with its own budget (`vreact.heartbeats`); since heartbeats spent
 * in an obligation still count for the enclosing command, the per-command `maxHeartbeats`
 * covers all obligations of the largest declaration of the file plus the declaration's own
 * elaboration and kernel check. An obligation that runs out of its budget may spend up to
 * 0.85 budgets more on finding the case that fails (`timeoutCases` in VReact/Tactic.lean),
 * so each obligation counts twice.
 */
function withBudget(text: string, perOb = OB_HEARTBEATS): string {
  const lines = text.split("\n");
  let most = 0;
  for (const d of leanDecls(text)) {
    const body = lines.slice(d.start - 1, d.end).join("\n");
    most = Math.max(most, (body.match(/\/-⟦ob\d+⟧-\//g) ?? []).length);
  }
  // 0 = no limit (for obligations, hence also for their declarations)
  const outer = perOb === 0 ? 0 : DECL_HEARTBEATS + 2 * perOb * most;
  return text.replace(BUDGET_SLOT, `set_option maxHeartbeats ${outer}\nset_option vreact.heartbeats ${perOb}`);
}

function header(imports: string[]): string {
  return [
    "/- Generated by vreact from VTS sources. Do not edit: edit the .tsx file. -/",
    "import VReact",
    ...imports.map((i) => `import ${i}`),
    "open VReact",
    // (a binder the translation forgot must be an error, not an auto-bound implicit)
    "set_option autoImplicit false",
    "set_option linter.unusedVariables false",
    BUDGET_SLOT,
    "noncomputable section",
    "",
  ].join("\n");
}

/** The modules a Lean file imports (over-approximated: every `import` line, comments removed). */
function leanImports(text: string): string[] {
  const code = text.replace(/\/-[\s\S]*?-\//g, " ").replace(/--.*$/gm, "");
  const out: string[] = [];
  for (const m of code.matchAll(/^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]*)$/gm)) out.push(...m[1].trim().split(/\s+/).filter(Boolean));
  return out;
}

/**
 * For each module (in import order, dependencies first): the user proof modules
 * `Proofs.<Up>` of the modules it imports, to be imported by its Defs.lean. An import that
 * would close a cycle (a proof file that itself imports, directly or not, the importing
 * module) is left out: those lemmas then help only the views, as for the module itself
 * (`Proofs.<Mod>` imports `VTS.<Mod>.Defs`, so it can never be imported by that Defs).
 */
function upstreamProofs(mods: { ns: string; deps: string[] }[], proofs: Map<string, string>): Map<string, string[]> {
  const proofOf = (ns: string) => "Proofs." + ns.split(".").slice(1).join(".");
  const edges = new Map<string, string[]>();
  const add = (from: string, to: string) => edges.set(from, [...(edges.get(from) ?? []), to]);
  for (const [p, text] of proofs) for (const i of leanImports(text)) add(p, i);
  for (const { ns, deps } of mods) {
    for (const d of deps) add(`${ns}.Defs`, `${d}.Defs`), add(`${ns}.View`, `${d}.View`);
    if (proofs.has("Proofs.Base")) add(`${ns}.Defs`, "Proofs.Base");
    add(`${ns}.View`, `${ns}.Defs`);
    if (proofs.has(proofOf(ns))) add(`${ns}.View`, proofOf(ns));
    add("VTS", `${ns}.View`); // the root module
  }
  const reaches = (from: string, to: string) => {
    const seen = new Set<string>();
    const go = (n: string): boolean => n === to || (!seen.has(n) && (seen.add(n), (edges.get(n) ?? []).some(go)));
    return go(from);
  };
  const out = new Map<string, string[]>();
  for (const { ns, deps } of mods) {
    const self = `${ns}.Defs`;
    for (const d of deps) {
      const p = proofOf(d);
      if (!proofs.has(p) || reaches(p, self)) continue;
      add(self, p);
      out.set(ns, [...(out.get(ns) ?? []), p]);
    }
  }
  return out;
}

/* ───────────────────────── declaration prepass ───────────────────────── */

function collect(st: ts.Statement, m: ModCtx, ns: string, res: TranslateResult) {
  const prog = m.prog;
  if (ts.isImportDeclaration(st)) return;
  if (ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) {
    typeOfDecl(st, prog.typeEnv);
    return;
  }
  if (ts.isFunctionDeclaration(st)) {
    if (!st.name) fail(st, "functions need a name");
    if (isAmbient(st)) fail(st, AMBIENT_MSG);
    if (!st.body) fail(st, "function overloads (declarations without a body) are not supported: declare the function once, with its body");
    if (st.asteriskToken || st.modifiers?.some((x) => x.kind === ts.SyntaxKind.AsyncKeyword)) fail(st, "async functions and generators are not supported");
    rejectGenericFunctionValues(st);
    const trusted = isTrusted(st);
    if (!trusted && st.body) rejectAsyncFunctions(st.body);
    if (isComponentDecl(st, prog)) {
      if (st.typeParameters?.length) fail(st.typeParameters[0], `generic components are not supported in VTS (${st.name.text}<${st.typeParameters.map((t) => t.name.text).join(", ")}>): give the props concrete types, and move generic code into a generic top-level function`);
      const info = compSignature(st, ns, ns, m, trusted);
      prog.globals.set(st, { k: "comp", info });
      return;
    }
    if (/^use[A-Z]/.test(st.name.text)) fail(st, "custom hooks are not supported yet: inline the hook calls into the component");
    checkValueNameFree(st.name, "function", m);
    if (trusted && st.typeParameters?.length) fail(st.typeParameters[0], TRUSTED_GENERIC_MSG(st.name.text, st.typeParameters.map((t) => t.name.text)));
    // type parameters first: the signature refers to them
    const tparams = registerTypeParams(st, prog.typeEnv);
    const params = st.parameters.map((p) => {
      checkNotThisParam(p);
      if (!p.type) fail(p, "parameters need type annotations");
      if (p.initializer || p.dotDotDotToken || p.questionToken) fail(p, "default/rest/optional parameters are not supported");
      if (!ts.isIdentifier(p.name)) fail(p, "destructured parameters are not supported in top-level functions");
      const t = typeOfNode(p.type, prog.typeEnv, capitalize(st.name!.text) + capitalize(p.name.text));
      if (t.k === "fn") {
        // (a direct callback parameter: say what to write instead)
        const fix = `a top-level function cannot take a callback (functions are not first-class in VTS); write the arrow at the call site instead (xs.find((x) => …), xs.filter(…))`;
        fail(p.type, st.typeParameters?.length
          ? `parameter ${p.name.text} is a function (${nodeText(p.type, 50)}): ${fix}, or let the generic function read what it needs through a field constraint (T extends { readonly done: boolean })`
          : `parameter ${p.name.text} has the function type ${showType(t)}, which is not data: ${fix}`);
      }
      checkValueType(p.type, t, prog.reg, `parameter ${p.name.text}`);
      return { name: p.name.text, type: t };
    });
    if (!st.type) fail(st, "functions need a return type annotation");
    const ret = typeOfNode(st.type, prog.typeEnv, capitalize(st.name.text) + "Result");
    checkValueType(st.type, ret, prog.reg, `the result of ${st.name.text}`);
    const hasPre = !!st.body?.statements.some((s) => isSpecCall(s, m, "requires"));
    const info: FnInfo = { qname: `${ns}.${leanIdent(st.name.text)}`, name: st.name.text, tparams, params, ret, hasPre, trusted, opaque: isOpaque(st), decl: st, module: ns };
    prog.globals.set(st, { k: "fn", info });
    return;
  }
  if (ts.isVariableStatement(st)) {
    if (isAmbient(st)) fail(st, AMBIENT_MSG);
    if (!(st.declarationList.flags & ts.NodeFlags.Const)) fail(st, "top-level variables must be const");
    rejectGenericFunctionValues(st);
    for (const d of st.declarationList.declarations) {
      if (!ts.isIdentifier(d.name) || !d.initializer) fail(d, "top-level const needs a name and initializer");
      checkValueNameFree(d.name, "constant", m);
      rejectAsyncFunctions(d.initializer);
      let t: VType | undefined = d.type ? typeOfNode(d.type, prog.typeEnv, capitalize(d.name.text)) : undefined;
      if (t) checkValueType(d.type!, t, prog.reg, `constant ${d.name.text}`);
      if (!t) {
        const init = d.initializer;
        if (ts.isNumericLiteral(init)) t = /[.eE]/.test(init.text) ? T.num : T.int;
        else if (ts.isPrefixUnaryExpression(init) && ts.isNumericLiteral(init.operand)) t = T.int;
        else if (ts.isStringLiteralLike(init)) t = T.str;
        else if (init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword) t = T.bool;
        else fail(d, "annotate the type of this constant");
      }
      prog.globals.set(d, { k: "const", info: { qname: `${ns}.${leanIdent(d.name.text)}`, type: t, decl: d, opaque: isOpaque(d) || isOpaque(st), facts: [] } });
    }
    return;
  }
  // `export { a, b as default }`, `export … from "./m"` (an import too: checked with the imports)
  // only (re-)bind names
  if (ts.isExportDeclaration(st)) return;
  if (ts.isExportAssignment(st)) {
    if (st.isExportEquals) fail(st, "`export =` is not supported: use `export` declarations or `export default x`");
    // `export default <expression>` evaluates the expression when the module loads: only a name
    // of the program (its initialisation order is checked: checkInitOrder)
    let e: ts.Expression = st.expression;
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    const d = ts.isIdentifier(e) ? prog.refDecl(e) : undefined;
    if (!d || prog.isLibraryFile(d.getSourceFile())) {
      fail(st, "`export default` of an expression is not supported (it would run unchecked when the module loads): declare a constant and export it (`export const x: T = …;` or `const x: T = …; export default x;`), or write `export default function …`");
    }
    return;
  }
  // module-level assert(fact): a proved fact about @opaque constants
  if (ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) && isSpecCall(st, m, "assert")) {
    const fact = st.expression.arguments[0];
    let owner: { info: { facts: ts.Expression[]; opaque: boolean } } | null = null;
    // (the fact is a theorem of its constant's module, which cannot see this module's
    // declarations: a constant imported from another module cannot own it)
    let imported: ts.VariableDeclaration | null = null;
    const visit = (n: ts.Node) => {
      if (owner || isErasedType(n)) return;
      if (ts.isIdentifier(n)) {
        const d = prog.refDecl(n);
        const g = d ? prog.globals.get(d) : undefined;
        if (g?.k === "const" && g.info.opaque) {
          if (d!.getSourceFile() === m.sf) owner = g as { info: ConstInfo };
          else imported ??= d as ts.VariableDeclaration;
        }
      }
      ts.forEachChild(n, visit);
    };
    visit(fact);
    if (!owner && imported) {
      const c = imported as ts.VariableDeclaration;
      fail(st, `a module-level assert(…) about \`${(c.name as ts.Identifier).text}\`, an /** @opaque */ constant of another module (${path.basename(c.getSourceFile().fileName)}), is not supported: a fact is proved in its constant's module; state it there, or about a constant of this module`);
    }
    if (!owner) fail(st, "a module-level assert(…) states a fact about an /** @opaque */ constant declared above it");
    (owner as { info: { facts: ts.Expression[] } }).info.facts.push(fact);
    return;
  }
  if (ts.isEmptyStatement(st)) return;
  if (ts.isModuleDeclaration(st)) fail(st, "`declare global`, `declare module` and namespaces are not supported in VTS: they can add to or change the types of library declarations (global augmentation, interface merging), which nothing checks");
  if (isAmbient(st)) fail(st, AMBIENT_MSG);
  fail(st, `top-level statement not supported in VTS (only imports, types, functions, components and constants)`);
}

/**
 * A function or constant must not share its name with a type of the module: TypeScript keeps
 * types and values apart (`type Limits = …; const Limits: Limits = …`), but both would be the
 * Lean declaration `VTS.<module>.Limits`.
 */
function checkValueNameFree(name: ts.Identifier, what: string, m: ModCtx) {
  const t = m.sf.statements.find((x) => (ts.isTypeAliasDeclaration(x) || ts.isInterfaceDeclaration(x)) && x.name.text === name.text);
  if (t) fail(name, `\`${name.text}\` names both a type (line ${m.sf.getLineAndCharacterOfPosition(t.getStart()).line + 1}) and a ${what} of this module: TypeScript keeps types and values apart, but in Lean both would be ${m.ns}.${leanIdent(name.text)}; rename one of them`);
}

const AMBIENT_MSG = "ambient declarations (`declare …`) are not supported: they state a type without code, which nothing checks (and `declare global` / `declare module` would change the types of library declarations)";

/** A `declare …` statement. */
function isAmbient(st: ts.Statement): boolean {
  return ts.canHaveModifiers(st) && !!ts.getModifiers(st)?.some((x) => x.kind === ts.SyntaxKind.DeclareKeyword);
}

/**
 * Module initialisation order.  JS runs a module's top-level statements in source order; a
 * `const` is in its temporal dead zone until its declaration has run, and reading it earlier
 * throws a ReferenceError — also from inside a function that the initialiser calls, which
 * TypeScript does not check (it flags direct reads only).  The Lean translation orders
 * declarations by dependency, so such a constant would get a value although the module throws
 * when it loads: rejected.  The code that runs at load is every constant's initialiser, a
 * module-level `assert(…)` and `export default x`; what it may read is every constant of the
 * module it mentions, directly or through the functions it calls (transitively; the lambdas of
 * `ensures` and `callbackRequires`, which JS never calls, excepted).  Imported constants are
 * initialised before the module runs (imports are acyclic).
 */
function checkInitOrder(sf: ts.SourceFile, m: ModCtx) {
  const prog = m.prog;
  const isConst = (d: ts.Node): d is ts.VariableDeclaration => d.getSourceFile() === sf && prog.globals.get(d)?.k === "const";
  /** what evaluating `n` may read: constants of this module, each with the chain of calls reaching it */
  type Reads = Map<ts.VariableDeclaration, string[]>;
  const memo = new Map<ts.FunctionDeclaration, Reads>();
  // (recursion is rejected elsewhere; a function met again while its body is scanned adds nothing)
  const visiting = new Set<ts.Node>();
  const reads = (n: ts.Node, out: Reads) => {
    const visit = (x: ts.Node) => {
      // a contract lambda is created, never called, by the running code
      if (ts.isCallExpression(x) && ["ensures", "callbackRequires"].includes(prog.specName(x.expression) ?? "")) {
        for (const a of x.arguments) if (!(ts.isArrowFunction(a) || ts.isFunctionExpression(a))) visit(a);
        return;
      }
      // (types are erased: nothing in them runs)
      if (isErasedType(x)) return;
      if (ts.isIdentifier(x)) {
        // (also the name of a shorthand property `{ B }`, which reads the variable B)
        const d = prog.refDecl(x);
        if (d && isConst(d)) {
          if (!out.has(d)) out.set(d, []);
        } else if (d && ts.isFunctionDeclaration(d) && d.getSourceFile() === sf && d.body && !visiting.has(d)) {
          for (const [c, path] of fnReads(d)) if (!out.has(c)) out.set(c, [d.name?.text ?? "?", ...path]);
        }
      }
      ts.forEachChild(x, visit);
    };
    visit(n);
  };
  const fnReads = (fn: ts.FunctionDeclaration): Reads => {
    const hit = memo.get(fn);
    if (hit) return hit;
    const out: Reads = new Map();
    visiting.add(fn);
    reads(fn.body!, out);
    visiting.delete(fn);
    memo.set(fn, out);
    return out;
  };
  const check = (at: ts.Node, what: string, code: ts.Node) => {
    const out: Reads = new Map();
    reads(code, out);
    for (const [c, via] of out) {
      if (c.getStart() < at.getStart()) continue;
      const name = (c.name as ts.Identifier).text;
      const how = via.length ? `calls ${via.map((f) => `\`${f}\``).join(", which calls ")}, which reads \`${name}\`` : `reads \`${name}\``;
      fail(at, `${what} ${how}${c === at ? " (itself)" : `, declared below it`}: JS evaluates a module's top-level code in order, and reading a constant before its declaration has run throws a ReferenceError when the module loads (TypeScript checks only direct reads). Declare \`${name}\` above it`);
    }
  };
  for (const st of sf.statements) {
    if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) if (d.initializer && isConst(d)) check(d, `the initialiser of \`${(d.name as ts.Identifier).text}\``, d.initializer);
    } else if (ts.isExpressionStatement(st)) {
      check(st, "this module-level statement", st.expression);
    } else if (ts.isExportAssignment(st)) {
      // (`export default f` of a function reads the hoisted function, it does not call it)
      const d = prog.refDecl(st.expression);
      if (!(d && ts.isFunctionDeclaration(d))) check(st, "`export default`", st.expression);
    }
  }
}

/**
 * Async functions and generators inside verified code: the translation gives a function the
 * meaning of its body run to completion, but an async function returns a promise (always
 * truthy: `xs.filter(async (x) => x > 3)` keeps every element) and runs what follows an
 * `await` later, and calling a generator does not run its body at all.
 */
function rejectAsyncFunctions(n: ts.Node) {
  const visit = (x: ts.Node) => {
    if ((ts.isArrowFunction(x) || ts.isFunctionExpression(x) || ts.isMethodDeclaration(x)) && (x.asteriskToken || x.modifiers?.some((k) => k.kind === ts.SyntaxKind.AsyncKeyword))) {
      fail(x, "async functions and generators are not supported in VTS: an async function returns a promise (always truthy, e.g. as a filter or some/every predicate) and runs the code after an `await` later, when e.g. an event's fields have changed; calling a generator does not run its body. Use a plain function");
    }
    ts.forEachChild(x, visit);
  };
  visit(n);
}

/**
 * A `@trusted` generic function would be one Lean axiom (and one per contract) quantified over
 * every Lean type `{T : Type}` with the constraint's binders — empty types, and types with other
 * values than the instantiations TypeScript allows (`T extends boolean` at `Int`, an accessor
 * that is not a field read) — which is stronger than its JS meaning and can be inconsistent
 * (`decode<T>(s: string): T` inhabits `Empty`).  Rejected.
 */
const TRUSTED_GENERIC_MSG = (name: string, tps: string[]) =>
  `a /** @trusted */ generic function (${name}<${tps.join(", ")}>) is not supported: Lean would assume its type and contracts for every type ${tps.join(", ")} (empty types, and types with values JS never passes, included), which is stronger than what it means in JavaScript and can be contradictory; verify it instead (remove @trusted; /** @opaque */ keeps its body hidden from callers), or write one @trusted function per concrete type`;

/**
 * Generic arrow functions and function expressions (`const id = <T,>(x: T) => x`): only top-level
 * functions may have type parameters (local helpers are inlined at their calls, where their type
 * parameters would have no binder).
 */
function rejectGenericFunctionValues(st: ts.Node) {
  const visit = (n: ts.Node) => {
    if ((ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && n.typeParameters?.length) {
      fail(n.typeParameters[0], `generic arrow functions and function expressions are not supported in VTS (type parameter ${n.typeParameters[0].name.text}): make the helper a generic top-level function`);
    }
    ts.forEachChild(n, visit);
  };
  ts.forEachChild(st, visit);
}

function isSpecCall(s: ts.Statement, m: ModCtx, name: string): boolean {
  if (!ts.isExpressionStatement(s) || !ts.isCallExpression(s.expression)) return false;
  const env = baseEnv(m);
  return specFn(env, s.expression.expression) === name;
}

/** Order constants and functions of a module so definitions precede uses. */
function sortDecls(sf: ts.SourceFile, m: ModCtx): ts.Node[] {
  const decls: ts.Node[] = [];
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && m.prog.globals.get(st)?.k === "fn") decls.push(st);
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (m.prog.globals.get(d)?.k === "const") decls.push(d);
  }
  return topo(decls, m, (g) => g.k === "fn" || g.k === "const");
}

/**
 * The functions of `decls` that another constant or function of the module refers to (in its
 * body or contracts, or in a module-level assert about it): their postconditions must stay in
 * Defs.lean, where those declarations' obligations may use them.
 */
function usedByOthers(decls: ts.Node[], m: ModCtx): Set<ts.Node> {
  const set = new Set(decls);
  const out = new Set<ts.Node>();
  const scan = (owner: ts.Node, n: ts.Node) => {
    if (isErasedType(n)) return;
    if (ts.isIdentifier(n)) {
      const dd = m.prog.refDecl(n);
      if (dd && dd !== owner && set.has(dd) && m.prog.globals.get(dd)?.k === "fn") out.add(dd);
    }
    ts.forEachChild(n, (c) => scan(owner, c));
  };
  for (const d of decls) {
    ts.forEachChild(d, (c) => scan(d, c));
    const g = m.prog.globals.get(d);
    if (g?.k === "const") for (const f of g.info.facts) scan(d, f);
  }
  return out;
}

function sortComponents(sf: ts.SourceFile, m: ModCtx): ts.Node[] {
  const comps = sf.statements.filter((st) => ts.isFunctionDeclaration(st) && m.prog.globals.get(st)?.k === "comp");
  return topo(comps, m, (g) => g.k === "comp");
}

function topo(decls: ts.Node[], m: ModCtx, rel: (g: Global) => boolean): ts.Node[] {
  const set = new Set(decls);
  const out: ts.Node[] = [];
  const st = new Map<ts.Node, number>();
  const refs = (d: ts.Node): ts.Node[] => {
    const r: ts.Node[] = [];
    const visit = (n: ts.Node) => {
      if (isErasedType(n)) return;
      if (ts.isIdentifier(n)) {
        const dd = m.prog.refDecl(n);
        if (dd && dd !== d && set.has(dd)) {
          const g = m.prog.globals.get(dd);
          if (g && rel(g)) r.push(dd);
        }
      }
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(d, visit);
    return r;
  };
  const go = (d: ts.Node) => {
    const s = st.get(d);
    if (s === 2) return;
    if (s === 1) fail(d, "mutually recursive declarations are not supported");
    st.set(d, 1);
    for (const x of refs(d)) go(x);
    st.set(d, 2);
    out.push(d);
  };
  for (const d of decls) go(d);
  return out;
}

/**
 * The reported items `nodes` use (in this or another module): functions and constants by
 * Lean name, components by namespace. The report uses them to follow the dependency cone
 * of an item (a declaration that did not elaborate breaks everything that uses it).
 */
function itemRefs(nodes: ts.Node[], self: ts.Node, m: ModCtx): string[] {
  const out = new Set<string>();
  const visit = (n: ts.Node) => {
    if (isErasedType(n)) return;
    if (ts.isIdentifier(n)) {
      const dd = m.prog.refDecl(n);
      const g = dd && dd !== self ? m.prog.globals.get(dd) : undefined;
      if (g) out.add(g.k === "comp" ? g.info.ns : g.info.qname);
    }
    ts.forEachChild(n, visit);
  };
  for (const n of nodes) ts.forEachChild(n, visit);
  return [...out];
}

/** Source text for a Lean doc comment: `/-` and `-/` (comments nest in Lean) must not occur in it. */
function docText(node: ts.Node, max: number): string {
  return nodeText(node, max).replace(/\/-/g, "/ -").replace(/-\//g, "- /");
}

/* ───────────────────────── constants & functions ───────────────────────── */

function translateConst(d: ts.VariableDeclaration, info: ConstInfo, m: ModCtx): string {
  const env = baseEnv(m);
  // closures in the initialiser (`[1].every((x) => { let y = 1; const g = () => y; y = 2; … })`)
  // must agree with JS, as in a function body
  checkClosures(d.initializer!, env);
  const v = expr(d.initializer!, env, info.type);
  const short = leanIdent((d.name as ts.Identifier).text);
  // transparent constants are unfolded by automation; @opaque ones only through their facts
  return `${info.opaque ? "" : "@[vreact_simp, reducible] "}def ${short} : ${leanType(info.type)} :=\n  ${v.code}\n`;
}

/** The theorem of the `k`-th module-level assert(…) about the constant `d` (emitted once what it mentions is declared). */
function translateFact(d: ts.VariableDeclaration, info: ConstInfo, k: number, m: ModCtx): string {
  const env = baseEnv(m);
  const short = leanIdent((d.name as ts.Identifier).text);
  const f = info.facts[k];
  const name = k === 0 ? `${short}.post` : `${short}.post${k + 1}`;
  checkClosures(f, env);
  const stmt = prop(f, env);
  // (`unfold` fails where the statement does not mention the constant)
  const unfold = stmt.includes(info.qname) ? `\n  unfold ${short}` : "";
  return `/-- fact: ${docText(f, 80)} -/\ntheorem ${name} : ${stmt} := by${unfold}\n  exact ${m.ob(f, "fact", `fact about ${short}: ${exprText(f)}`)}\n`;
}

/**
 * The declarations of `decls` (functions and constants of the module) that the fact `f` mentions:
 * its theorem must come after all of them.  (A module-level assert runs after the declarations
 * above it, and function declarations are hoisted: a fact may call a function declared below
 * the constant it is about.)
 */
function factDeps(f: ts.Expression, decls: Set<ts.Node>, m: ModCtx): ts.Node[] {
  const out: ts.Node[] = [];
  const visit = (n: ts.Node) => {
    if (isErasedType(n)) return;
    if (ts.isIdentifier(n)) {
      const dd = m.prog.refDecl(n);
      if (dd && decls.has(dd)) out.push(dd);
    }
    ts.forEachChild(n, visit);
  };
  visit(f);
  return out;
}

function hasHole(fn: ts.FunctionDeclaration, m: ModCtx): boolean {
  let found = false;
  const visit = (n: ts.Node) => {
    if (ts.isCallExpression(n) && m.prog.specName(n.expression) === "hole") found = true;
    if (!found) ts.forEachChild(n, visit);
  };
  if (fn.body) visit(fn.body);
  return found;
}

function translateFunction(fn: ts.FunctionDeclaration, info: FnInfo, m: ModCtx): { def: string; post: string | null; postNames: string[] } {
  let env = baseEnv(m);
  // a generic function: its type binders, the `[DecidableEq T]` of equality constraints and the
  // accessor parameters of field constraints come first, in this order — the same telescope for
  // the definition and every contract theorem (`vreact_contracts` applies a theorem to a call's
  // whole argument list).  TypeScript's type and value names are separate, Lean's are not: the
  // value parameters and locals avoid these names (`env.scope`).
  const binders: string[] = [];
  const typeArgs: string[] = [];
  const argNames: string[] = [];
  if (info.tparams.length) {
    const scope = new Set(env.scope);
    for (const p of info.tparams) {
      binders.push(`{${p.lean} : Type}`);
      typeArgs.push(`(${p.lean} := ${p.lean})`);
      scope.add(p.lean);
    }
    for (const p of info.tparams) if (p.eq) binders.push(`[DecidableEq ${p.lean}]`);
    for (const p of info.tparams) {
      for (const f of p.fields ?? []) {
        binders.push(`(${f.acc} : ${p.lean} → ${leanType(f.type)})`);
        argNames.push(f.acc);
        scope.add(f.acc);
      }
    }
    env = { ...env, scope };
  }
  fn.parameters.forEach((p, i) => {
    const r = bindParam(p.name, info.params[i].type, env);
    env = r.env;
    binders.push(`(${r.binder} : ${leanType(info.params[i].type)})`);
    argNames.push(r.binder);
  });
  const stmts = [...(fn.body?.statements ?? [])];
  const hyps: string[] = [];
  const hypNames: string[] = [];
  const reqs: ts.Expression[] = [];
  const posts: { lam: ts.ArrowFunction | ts.FunctionExpression }[] = [];
  const contractStmts: ts.Statement[] = [];
  while (stmts.length && ts.isExpressionStatement(stmts[0]) && ts.isCallExpression(stmts[0].expression)) {
    const c = stmts[0].expression;
    const sf = specFn(env, c.expression);
    if (sf === "requires") {
      if (c.arguments.length !== 1) fail(c, "requires(condition)");
      reqs.push(c.arguments[0]);
    } else if (sf === "ensures") {
      const lam = c.arguments[0];
      if (!lam || !(ts.isArrowFunction(lam) || ts.isFunctionExpression(lam)) || lam.parameters.length !== 1) fail(c, "ensures((result) => condition)");
      posts.push({ lam });
    } else if (sf === "decreases") {
      fail(c, "recursion is not supported yet");
    } else break;
    contractStmts.push(stmts.shift()!);
  }
  // the contracts of a @trusted function are translated although its body is not: closures in
  // them (a block-bodied every/some callback, read as code) must agree with JS, as in a verified
  // body (whose check, in valueBlock, covers its contracts too)
  if (info.trusted && fn.body) checkClosures(fn.body, env, contractStmts);
  // all requires form one precondition (each guarded by the earlier ones): call sites pass one proof
  if (reqs.length) {
    hyps.push(`(h_pre : ${propAll(reqs, env)})`);
    hypNames.push("h_pre");
  }
  const short = leanIdent(info.name);
  const sig = `${short} ${binders.join(" ")} ${hyps.join(" ")} : ${leanType(info.ret)}`.replace(/\s+/g, " ");
  let def: string;
  if (info.trusted) {
    def = `/-- @trusted: body not verified, contract assumed. -/\naxiom ${sig}\n`;
  } else {
    // self-recursion check
    let rec = false;
    const visit = (n: ts.Node) => {
      // (by the declaration the callee resolves to: a local helper spelled like the function is not it)
      if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && m.prog.refDecl(n.expression) === fn) rec = true;
      ts.forEachChild(n, visit);
    };
    stmts.forEach(visit);
    if (rec) fail(fn, "recursion is not supported yet: use array methods or for…of");
    const body = valueBlock(stmts, env, info.ret, fn);
    def = `${info.opaque ? "" : "@[vreact_simp, reducible] "}def ${sig} :=\n  ${body.code}\n`;

  }
  let post: string | null = null;
  const postNames: string[] = [];
  if (posts.length) {
    // (type arguments by name: a type parameter may occur in the result type only)
    const call = `(${info.qname}${[...typeArgs, ...argNames, ...hypNames].map((a) => " " + a).join("")})`;
    const kw = info.trusted ? "axiom" : "theorem";
    const parts: string[] = [];
    posts.forEach(({ lam }, k) => {
      const p = lam.parameters[0];
      if (!ts.isIdentifier(p.name)) fail(p, "result parameter must be an identifier");
      // `ensures` takes `(result: any) => boolean`: TypeScript never checks the annotation, so it
      // must be exactly the declared return type (the null/undefined checks read it)
      const retTs = m.checker.getTypeFromTypeNode(fn.type!);
      checkParamAnnotation(p, info.ret, retTs, env);
      const e2 = { ...env, vars: new Map(env.vars) };
      e2.vars.set(symbolOf(env, p.name)!, { k: "val", code: call, type: info.ret, ts: retTs });
      const body = lam.body;
      if (ts.isBlock(body)) fail(body, "ensures body must be an expression");
      const stmt = prop(body, e2);
      const name = k === 0 ? `${short}.post` : `${short}.post${k + 1}`;
      postNames.push(`${info.module}.${short}.${k === 0 ? "post" : `post${k + 1}`}`);
      // opaque functions are not unfolded by callers: their postconditions are proved by
      // unfolding once here, then used through E-matching on calls (grind_pattern below)
      // a function whose body still contains hole() has no implementation yet: contract pending
      const pending = hasHole(fn, m);
      const ob = info.trusted || pending ? "" : m.ob(lam, "postcondition", `postcondition of ${info.name}: ${exprText(body)}`);
      // (`unfold` fails where the statement does not mention the function: a contract that does
      // not use its result, e.g. a fact about the arguments)
      const unfold = stmt.includes(call) ? `\n  unfold ${short}` : "";
      const proof = info.trusted ? "" : pending ? ` :=\n  sorry /- pending: hole() -/` : info.opaque ? ` := by${unfold}\n  exact ${ob}` : ` :=\n  ${ob}`;
      let t = `${kw} ${name} ${binders.join(" ")} ${hyps.join(" ")} :\n    ${stmt}${proof}\n`;
      parts.push(t);
    });
    post = parts.join("\n");
  }
  return { def, post, postNames };
}
