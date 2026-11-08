import ts from "typescript";
import { fail, leanField, leanAccessor, leanIdent, leanStr, jsStr, capitalize, subscripted, INSTANCE_NAME_RE } from "./util.ts";

/**
 * VTS types.  Every TypeScript type accepted by the subset maps to one of these,
 * and each of these maps to a Lean type:
 *
 *   boolean → Bool, int → Int, number → Float, string → String,
 *   "a" | "b" (string literal union) → inductive enum,
 *   { … } / interface → structure,
 *   discriminated union of objects → inductive with one constructor per variant,
 *   readonly T[] / T[] → List T,  T | null / T | undefined / f?: T → Option T,
 *   [A, B] → A × B.
 */
export type VType =
  | { k: "bool" }
  | { k: "int" }
  | { k: "num" }
  | { k: "str" }
  | { k: "unit" }
  | { k: "void" }
  | { k: "node" }
  | { k: "enum"; name: string }
  | { k: "rec"; name: string }
  | { k: "union"; name: string }
  | { k: "arr"; elem: VType }
  | { k: "opt"; elem: VType }
  | { k: "tuple"; elems: VType[] }
  | { k: "fn"; params: Param[]; ret: VType }
  /**
   * A type parameter of a generic top-level function (identified by `id`: one per declaration),
   * abstract in the function's body.  `eq`: equality constraint (`T extends int | string`, Lean
   * `[DecidableEq T]`); `fields`: field constraint (`T extends { readonly id: int }`, one Lean
   * accessor parameter `acc : T → U` per field).  Instantiations are closed, non-optional types.
   */
  | { k: "tvar"; name: string; lean: string; id: number; eq: boolean; fields: TField[] | null };

/** A field of a type parameter's field constraint, read through the accessor parameter `acc`. */
export interface TField {
  name: string;
  type: VType;
  acc: string;
}

/**
 * A type parameter of a generic top-level function, as the translator knows it (registered when
 * the function's signature is collected; a reference to an unregistered type parameter — of a
 * generic arrow, a component, a type — is rejected).
 */
export interface TParam {
  /** the TypeScript name (messages) */
  name: string;
  /** the Lean binder name `{T : Type}` */
  lean: string;
  id: number;
  decl: ts.TypeParameterDeclaration;
  eq: boolean;
  fields: TField[] | null;
  /** the TypeScript types of the constraint's fields (their null/undefined kinds) */
  fieldTs: Map<string, ts.Type>;
}

export function tvarOf(p: TParam): VType {
  return { k: "tvar", name: p.name, lean: p.lean, id: p.id, eq: p.eq, fields: p.fields };
}

/**
 * Types whose values JS compares by value with `===` (and SameValueZero: `includes`, `indexOf`,
 * a Set, a Map key), exactly as Lean's `=` does: booleans, ints, strings, string-literal enums,
 * and type parameters with an equality constraint (instantiated only with these).  Not `number`
 * (NaN, -0) and not objects/arrays (identity).
 */
export function isEqType(t: VType): boolean {
  return t.k === "bool" || t.k === "int" || t.k === "str" || t.k === "enum" || (t.k === "tvar" && t.eq);
}

/** Whether `t` mentions a type parameter (one of `ids`, or any when `ids` is omitted). */
export function mentionsTVar(t: VType, ids?: ReadonlySet<number>): boolean {
  switch (t.k) {
    case "tvar":
      return !ids || ids.has(t.id);
    case "arr":
    case "opt":
      return mentionsTVar(t.elem, ids);
    case "tuple":
      return t.elems.some((e) => mentionsTVar(e, ids));
    case "fn":
      return t.params.some((p) => mentionsTVar(p.type, ids)) || mentionsTVar(t.ret, ids);
    default:
      return false;
  }
}

/** `t` with the type parameters of `σ` (by id) replaced by their instantiations. */
export function substType(t: VType, σ: ReadonlyMap<number, VType>): VType {
  switch (t.k) {
    case "tvar":
      return σ.get(t.id) ?? t;
    case "arr":
      return T.arr(substType(t.elem, σ));
    case "opt":
      return T.opt(substType(t.elem, σ));
    case "tuple":
      return { k: "tuple", elems: t.elems.map((e) => substType(e, σ)) };
    case "fn":
      return { k: "fn", params: t.params.map((p) => ({ name: p.name, type: substType(p.type, σ) })), ret: substType(t.ret, σ) };
    default:
      return t;
  }
}

export interface Param {
  name: string;
  type: VType;
}
export interface Field {
  name: string;
  type: VType;
}
export interface Variant {
  lit: string;
  ctor: string;
  fields: Field[];
}

export type TypeDef =
  | { k: "enum"; lits: string[] }
  | { k: "rec"; fields: Field[] }
  | { k: "union"; tag: string; variants: Variant[] };

export interface NamedType {
  /** Lean fully-qualified name. */
  qname: string;
  short: string;
  module: string;
  def: TypeDef;
  decl?: ts.Node;
}

export const T = {
  bool: { k: "bool" } as VType,
  int: { k: "int" } as VType,
  num: { k: "num" } as VType,
  str: { k: "str" } as VType,
  unit: { k: "unit" } as VType,
  void: { k: "void" } as VType,
  node: { k: "node" } as VType,
  arr: (elem: VType): VType => ({ k: "arr", elem }),
  opt: (elem: VType): VType => ({ k: "opt", elem }),
};

/** Registry of all named (nominal in Lean) types of the program. */
export class TypeRegistry {
  byName = new Map<string, NamedType>();
  byDecl = new Map<ts.Node, NamedType>();
  /**
   * Inline (anonymous) record and enum types by module and structure: TypeScript types are
   * structural, so `hole<{ readonly v: int }>()` returned from a function declared to return
   * `{ readonly v: int }` (or an annotation spelling the same inline type) is one Lean type.
   */
  byShape = new Map<string, NamedType>();
  /** Per-module emission order. */
  order: NamedType[] = [];
  /** The type parameters of the program's generic functions, by declaration and by id. */
  tparams = new Map<ts.Node, TParam>();
  tparamById = new Map<number, TParam>();

  get(qname: string): NamedType {
    const t = this.byName.get(qname);
    if (!t) throw new Error("internal: unknown type " + qname);
    return t;
  }
  add(t: NamedType): NamedType {
    if (this.byName.has(t.qname)) {
      const existing = this.byName.get(t.qname)!;
      if (existing.decl !== t.decl) fail(t.decl, `duplicate type name ${t.short} in module ${t.module}`);
      return existing;
    }
    this.byName.set(t.qname, t);
    if (t.decl) this.byDecl.set(t.decl, t);
    this.order.push(t);
    return t;
  }
  rec(t: VType): Field[] {
    if (t.k !== "rec") throw new Error("internal: not a record");
    const d = this.get(t.name).def;
    if (d.k !== "rec") throw new Error("internal");
    return d.fields;
  }
  union(t: VType): { tag: string; variants: Variant[] } {
    if (t.k !== "union") throw new Error("internal: not a union");
    const d = this.get(t.name).def;
    if (d.k !== "union") throw new Error("internal");
    return d;
  }
  enumLits(t: VType): string[] {
    if (t.k !== "enum") throw new Error("internal: not an enum");
    const d = this.get(t.name).def;
    if (d.k !== "enum") throw new Error("internal");
    return d.lits;
  }
}

// (every kind is handled explicitly in the functions below, without a `default`: a new kind
// must be considered at each of them, and tsc reports a missing case)
export function sameType(a: VType, b: VType): boolean {
  if (a.k !== b.k) return false;
  switch (a.k) {
    case "bool":
    case "int":
    case "num":
    case "str":
    case "unit":
    case "void":
    case "node":
      return true;
    case "enum":
    case "rec":
    case "union":
      return a.name === (b as typeof a).name;
    case "arr":
    case "opt":
      return sameType(a.elem, (b as typeof a).elem);
    case "tuple": {
      const bb = b as typeof a;
      return a.elems.length === bb.elems.length && a.elems.every((e, i) => sameType(e, bb.elems[i]));
    }
    case "fn": {
      const bb = b as typeof a;
      return a.params.length === bb.params.length && a.params.every((p, i) => sameType(p.type, bb.params[i].type)) && sameType(a.ret, bb.ret);
    }
    case "tvar":
      // by declaration: two functions' `T` are different variables
      return a.id === (b as typeof a).id;
  }
}

export function showType(t: VType): string {
  switch (t.k) {
    case "bool":
      return "boolean";
    case "int":
      return "int";
    case "num":
      return "number";
    case "str":
      return "string";
    case "unit":
      return "{}";
    case "void":
      return "void";
    case "node":
      return "ReactNode";
    case "enum":
    case "rec":
    case "union":
      // the TypeScript name (Lean names may be quoted or primed, see leanIdent)
      return t.name.split(".").pop()!.replace(/^«(.*)»$/, "$1").replace(/'$/, "");
    case "arr":
      // `readonly (int | null)[]`, not `readonly int | null[]`
      return `readonly ${t.elem.k === "opt" || t.elem.k === "fn" ? `(${showType(t.elem)})` : showType(t.elem)}[]`;
    case "opt":
      return `${t.elem.k === "fn" ? `(${showType(t.elem)})` : showType(t.elem)} | null`;
    case "tuple":
      return `[${t.elems.map(showType).join(", ")}]`;
    case "fn":
      return `(${t.params.map((p) => `${p.name}: ${showType(p.type)}`).join(", ")}) => ${showType(t.ret)}`;
    case "tvar":
      return t.name;
  }
}

/** A canonical string of a VTS type (nominal types by name, type parameters by declaration). */
export function typeKey(t: VType): string {
  switch (t.k) {
    case "bool":
    case "int":
    case "num":
    case "str":
    case "unit":
    case "void":
    case "node":
      return t.k;
    case "enum":
    case "rec":
    case "union":
      return `${t.k}:${t.name}`;
    case "arr":
      return `[${typeKey(t.elem)}]`;
    case "opt":
      return `?(${typeKey(t.elem)})`;
    case "tuple":
      return `(${t.elems.map(typeKey).join(",")})`;
    case "fn":
      return `fn(${t.params.map((p) => typeKey(p.type)).join(",")})=>${typeKey(t.ret)}`;
    case "tvar":
      return `tvar:${t.id}`;
  }
}

/**
 * The type parameter declarations of the program's generic functions (`registerTypeParams`):
 * their instantiations are never null or undefined, so a type-parameter part of a TypeScript type
 * adds no nullish value (see `kindsOfType`).
 */
const vtsTypeParamDecls = new WeakSet<ts.Node>();

/** A type parameter of a VTS generic function (never instantiated with a nullish type)? */
function isVtsTypeParam(t: ts.Type): boolean {
  if (!(t.flags & ts.TypeFlags.TypeParameter)) return false;
  const d = t.symbol?.declarations?.[0];
  return !!d && vtsTypeParamDecls.has(d);
}

/**
 * Which nullish values (`null`, `undefined`) a TypeScript type admits (VTS represents both as
 * `none`; TypeScript types tell which one a value can be).  `null` when the type does not tell
 * (`any`, `unknown`, a type parameter other than a VTS generic function's: e.g. a callback
 * parameter annotated `unknown`, which TypeScript accepts for an argument of any type).  A type
 * parameter of a VTS generic function is never instantiated with a nullish type (the
 * translator checks every instantiation), so it adds neither (`T | null` admits `null` only).
 */
export function kindsOfType(t: ts.Type): { null: boolean; undef: boolean } | null {
  const parts = (t.isUnion() ? t.types : [t]).filter((p) => !isVtsTypeParam(p));
  if (parts.some((p) => (p.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.InstantiableNonPrimitive)) !== 0)) return null;
  return {
    null: parts.some((p) => (p.flags & ts.TypeFlags.Null) !== 0),
    undef: parts.some((p) => (p.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Void)) !== 0),
  };
}

/**
 * The nullish kinds a TypeScript type `t` of VTS type `vt` admits at each optional position
 * (`?n`, `?u`, `?nu`), as a string; null when TypeScript does not tell (`unknown`, `any`).
 * Records, unions and enums are nominal: their fields' kinds are those of their declaration.
 */
export function nullShape(t: ts.Type, vt: VType, ck: ts.TypeChecker): string | null {
  switch (vt.k) {
    case "opt": {
      const k = kindsOfType(t);
      const inner = k && nullShape(ck.getNonNullableType(t), vt.elem, ck);
      return k && inner !== null ? `?${k.null ? "n" : ""}${k.undef ? "u" : ""}(${inner})` : null;
    }
    case "arr": {
      const et = ck.getIndexTypeOfType(t, ts.IndexKind.Number);
      const inner = et ? nullShape(et, vt.elem, ck) : null;
      return inner === null ? null : `[${inner}]`;
    }
    case "tuple": {
      if (!ck.isTupleType(t)) return null;
      const args = ck.getTypeArguments(t as ts.TypeReference);
      if (args.length !== vt.elems.length) return null;
      const inner = vt.elems.map((e, i) => nullShape(args[i], e, ck));
      return inner.some((x) => x === null) ? null : `(${inner.join(",")})`;
    }
    case "bool":
    case "int":
    case "num":
    case "str":
    case "unit":
    case "void":
    case "node":
    case "fn":
    case "enum":
    case "rec":
    case "union":
      // (records, unions, enums: nominal, their fields' kinds are those of their declaration)
      return "";
    case "tvar":
      // a value of a type parameter: abstract (what its instantiation contains is not looked at
      // where the type parameter is in scope), and never nullish itself
      return "";
  }
}

/** The Lean type of a VTS type. */
export function leanType(t: VType): string {
  switch (t.k) {
    case "bool":
      return "Bool";
    case "int":
      return "Int";
    case "num":
      return "Float";
    case "str":
      return "VReact.JS.Str";
    case "unit":
    case "void":
      return "Unit";
    case "node":
      throw new Error("internal: node type has no Lean value type");
    case "enum":
    case "rec":
    case "union":
      return t.name;
    case "arr":
      return `(List ${leanType(t.elem)})`;
    case "opt":
      return `(Option ${leanType(t.elem)})`;
    case "tuple":
      return "(" + t.elems.map(leanType).join(" × ") + ")";
    case "fn":
      throw new Error("internal: function type has no Lean value type");
    case "tvar":
      return t.lean;
  }
}

/** Whether Lean can derive `DecidableEq` (Floats and functions cannot). */
export function hasDecEq(t: VType, reg: TypeRegistry, seen = new Set<string>()): boolean {
  switch (t.k) {
    case "bool":
    case "int":
    case "str":
    case "unit":
    case "void":
    case "enum":
      return true;
    case "num":
    case "fn":
    case "node":
      return false;
    case "tvar":
      // (only where its `[DecidableEq T]` binder is in scope)
      return t.eq;
    case "arr":
    case "opt":
      return hasDecEq(t.elem, reg, seen);
    case "tuple":
      return t.elems.every((e) => hasDecEq(e, reg, seen));
    case "rec":
    case "union": {
      if (seen.has(t.name)) return true;
      seen.add(t.name);
      const d = reg.get(t.name).def;
      if (d.k === "rec") return d.fields.every((f) => hasDecEq(f.type, reg, seen));
      if (d.k === "union") return d.variants.every((v) => v.fields.every((f) => hasDecEq(f.type, reg, seen)));
      return true;
    }
  }
}

/** Lean declaration text for a named type. */
export function emitTypeDecl(nt: NamedType, reg: TypeRegistry): string {
  const short = nt.short;
  const d = nt.def;
  const deq = hasDecEq({ k: nt.def.k as "rec", name: nt.qname }, reg);
  const deriv = deq ? "deriving Repr, DecidableEq" : "deriving Repr";
  if (d.k === "rec") {
    const fields = d.fields.map((f) => `  ${leanField(f.name)} : ${leanType(f.type)}`).join("\n");
    return `structure ${short} where\n${fields}\n${deriv}\n`;
  }
  if (d.k === "enum") {
    const ctors = d.lits.map((l) => `  | ${leanField(l)}`).join("\n");
    const toJs = d.lits.map((l) => `  | .${leanField(l)} => ${jsStr(l)}`).join("\n");
    // each member's string, unfolded by the automation on a known member (`toJS'`, `str'`: primed
    // names are never constructor names, see `leanAccessor`)
    return (
      `inductive ${short} where\n${ctors}\n${deriv}\n\n` +
      `/-- The string of each member. -/\n@[vreact_simp] def ${short}.toJS' : ${short} → VReact.JS.Str\n${toJs}\n\n` +
      `instance : VReact.JS.ToJS ${short} := ⟨${short}.toJS'⟩\n\n` +
      `@[vreact_simp] theorem ${short}.str' (x : ${short}) : VReact.JS.str x = ${short}.toJS' x := rfl\n`
    );
  }
  // union
  const ctors = d.variants
    .map((v) => `  | ${leanField(v.ctor)}` + v.fields.map((f) => ` (${leanIdent(f.name)} : ${leanType(f.type)})`).join(""))
    .join("\n");
  let out = `inductive ${short} where\n${ctors}\n${deriv}\n`;
  // the discriminant as a string
  out += `\ndef ${short}.${leanAccessor(d.tag)} : ${short} → VReact.JS.Str\n`;
  for (const v of d.variants) {
    out += `  | .${leanField(v.ctor)}${v.fields.map(() => " _").join("")} => ${jsStr(v.lit)}\n`;
  }
  // accessors for fields shared (same name & type) by all variants
  const shared = sharedFields(d.variants);
  for (const f of shared) {
    out += `\ndef ${short}.${leanAccessor(f.name)} : ${short} → ${leanType(f.type)}\n`;
    for (const v of d.variants) {
      // (the binder `x'` is never a constructor name, which a pattern variable would denote in the type's namespace)
      const pats = v.fields.map((g) => (g.name === f.name ? "x'" : "_")).join(" ");
      out += `  | .${leanField(v.ctor)} ${pats} => x'\n`;
    }
  }
  return out;
}

export function sharedFields(variants: Variant[]): Field[] {
  if (variants.length === 0) return [];
  return variants[0].fields.filter((f) => variants.every((v) => v.fields.some((g) => g.name === f.name && sameType(g.type, f.type))));
}

/** Lean pattern binding all fields of a variant with the given variable names. */
export function variantPattern(v: Variant, names: string[]): string {
  return `.${leanField(v.ctor)}${names.map((n) => " " + n).join("")}`;
}

/**
 * Conversion of TypeScript type syntax into VTS types.
 * `resolveRef` resolves a type reference to its declaration (provided by the module translator).
 */
export interface TypeEnv {
  checker: ts.TypeChecker;
  reg: TypeRegistry;
  /** Lean namespace for types declared in the given source file. */
  nsOf(sf: ts.SourceFile): string;
  /** Whether a type reference denotes `int` from vreact/spec. */
  isSpecInt(node: ts.TypeReferenceNode): boolean;
}

export function typeOfNode(node: ts.TypeNode, env: TypeEnv, hint: string): VType {
  switch (node.kind) {
    case ts.SyntaxKind.BooleanKeyword:
      return T.bool;
    case ts.SyntaxKind.StringKeyword:
      return T.str;
    case ts.SyntaxKind.NumberKeyword:
      return T.num;
    case ts.SyntaxKind.VoidKeyword:
      return T.void;
    case ts.SyntaxKind.ParenthesizedType:
      return typeOfNode((node as ts.ParenthesizedTypeNode).type, env, hint);
    case ts.SyntaxKind.TypeOperator: {
      const op = node as ts.TypeOperatorNode;
      if (op.operator === ts.SyntaxKind.ReadonlyKeyword) return typeOfNode(op.type, env, hint);
      fail(node, `type operator not supported in VTS: ${node.getText()}`);
    }
    case ts.SyntaxKind.ArrayType:
      return T.arr(typeOfNode((node as ts.ArrayTypeNode).elementType, env, hint + "Item"));
    case ts.SyntaxKind.TupleType: {
      const tt = node as ts.TupleTypeNode;
      return { k: "tuple", elems: tt.elements.map((e, i) => typeOfNode(ts.isNamedTupleMember(e) ? e.type : e, env, hint + i)) };
    }
    case ts.SyntaxKind.TypeLiteral:
      return recordFromMembers((node as ts.TypeLiteralNode).members, env, hint, node, node.getSourceFile());
    case ts.SyntaxKind.FunctionType: {
      const ft = node as ts.FunctionTypeNode;
      if (ft.typeParameters?.length) fail(node, `generic function types are not supported in VTS (${node.getText()}): only top-level functions may have type parameters`);
      const params = ft.parameters.map((p) => {
        if (!p.type) fail(p, "callback parameters need type annotations");
        return { name: p.name.getText(), type: typeOfNode(p.type, env, hint + capitalize(p.name.getText())) };
      });
      return { k: "fn", params, ret: typeOfNode(ft.type, env, hint + "Result") };
    }
    case ts.SyntaxKind.UnionType:
      return unionType(node as ts.UnionTypeNode, env, hint, undefined);
    case ts.SyntaxKind.LiteralType: {
      const lt = node as ts.LiteralTypeNode;
      if (ts.isStringLiteral(lt.literal)) {
        return enumType([lt.literal.text], env, hint, undefined, node.getSourceFile());
      }
      fail(node, `literal type not supported here: ${node.getText()}`);
    }
    case ts.SyntaxKind.TypeReference:
      return typeRef(node as ts.TypeReferenceNode, env, hint);
    default:
      fail(node, `type not supported in VTS: ${node.getText()}`);
  }
}

function typeRef(node: ts.TypeReferenceNode, env: TypeEnv, hint: string): VType {
  const name = node.typeName.getText();
  if (env.isSpecInt(node)) return T.int;
  const args = node.typeArguments ?? [];
  if ((name === "ReadonlyArray" || name === "Array") && args.length === 1) {
    return T.arr(typeOfNode(args[0], env, hint + "Item"));
  }
  if (["ReactNode", "React.ReactNode", "JSX.Element", "React.JSX.Element", "ReactElement", "React.ReactElement"].includes(name)) {
    return T.node;
  }
  let sym = env.checker.getSymbolAtLocation(node.typeName);
  if (!sym) fail(node, `cannot resolve type ${name}`);
  if (sym.flags & ts.SymbolFlags.Alias) sym = env.checker.getAliasedSymbol(sym);
  const decl = sym.declarations?.[0];
  if (!decl) fail(node, `cannot resolve type ${name}`);
  if (ts.isTypeParameterDeclaration(decl)) {
    const p = env.reg.tparams.get(decl);
    if (p) return tvarOf(p);
    fail(node, foreignTypeParam(decl));
  }
  if (args.length) fail(node, `generic type ${name}<…> not supported in VTS`);
  if (inProgress.has(decl)) fail(node, `type ${name} refers to itself: recursive types are not supported in VTS (use an array of records with ids, e.g. a parent id field)`);
  return typeOfDecl(decl, env);
}

/** Why a reference to a type parameter that is not a (registered) generic function's is rejected. */
function foreignTypeParam(decl: ts.TypeParameterDeclaration): string {
  const o = decl.parent;
  const n = decl.name.text;
  if (ts.isArrowFunction(o) || ts.isFunctionExpression(o)) {
    return `generic arrow functions and function expressions are not supported in VTS (type parameter ${n}): make the helper a generic top-level function`;
  }
  if (ts.isTypeAliasDeclaration(o)) return "generic type aliases are not supported in VTS";
  if (ts.isInterfaceDeclaration(o)) return "generic interfaces are not supported in VTS";
  if (ts.isFunctionDeclaration(o)) return `the type parameter ${n} of ${o.name?.text ?? "this function"} is not supported (only top-level functions that are not components may be generic)`;
  return `the type parameter ${n} is not supported here (only top-level functions may be generic)`;
}

let tparamCounter = 0;

/**
 * Register the type parameters of a generic top-level function (before its signature is
 * converted, so that references to them are type variables) and read their constraints:
 *  - none: abstract (passed, stored, returned; no operation looks into its values);
 *  - an equality constraint `T extends int | string | boolean | <enum> | "lit"` (unions of these):
 *    `===`, `includes`, `indexOf`, `distinct` on T (Lean `[DecidableEq T]`);
 *  - a field constraint `T extends { readonly id: int; … }` (or a named object type): `x.id` on
 *    `x : T`, through one explicit accessor parameter per field (`(T_id : T → Int)`).
 * Anything else is rejected.  Idempotent.
 */
export function registerTypeParams(fn: ts.FunctionDeclaration, env: TypeEnv): TParam[] {
  const tps = fn.typeParameters ?? [];
  const known = tps.map((tp) => env.reg.tparams.get(tp));
  if (known.every((p) => p)) return known as TParam[];
  const fname = fn.name?.text ?? "f";
  const used = new Set<string>();
  const out: TParam[] = [];
  for (const tp of tps) {
    const name = tp.name.text;
    if (tp.modifiers?.length) fail(tp, `\`${tp.modifiers.map((m) => m.getText()).join(" ")}\` type parameters are not supported in VTS: write ${fname}<${name}, …>`);
    if (tp.default) fail(tp.default, `default type arguments are not supported in VTS (${name} = ${tp.default.getText()}): where ${name} cannot be inferred from the arguments, callers write it (${fname}<…>(…))`);
    // (TypeScript's type names are distinct, and `leanIdent` is injective)
    const p: TParam = { name, lean: leanIdent(name), id: ++tparamCounter, decl: tp, eq: false, fields: null, fieldTs: new Map() };
    used.add(p.lean);
    out.push(p);
  }
  for (const p of out) {
    env.reg.tparams.set(p.decl, p);
    env.reg.tparamById.set(p.id, p);
    vtsTypeParamDecls.add(p.decl);
  }
  for (const p of out) readConstraint(p, fname, env, used);
  return out;
}

/** Does a type node refer to a type parameter? */
function mentionsTypeParam(n: ts.Node, ck: ts.TypeChecker): boolean {
  let found = false;
  const visit = (x: ts.Node) => {
    if (found) return;
    if (ts.isTypeReferenceNode(x)) {
      let s = ck.getSymbolAtLocation(x.typeName);
      if (s && s.flags & ts.SymbolFlags.Alias) s = ck.getAliasedSymbol(s);
      if (s?.declarations?.some((d) => ts.isTypeParameterDeclaration(d))) found = true;
    }
    ts.forEachChild(x, visit);
  };
  visit(n);
  return found;
}

const CONSTRAINT_FORMS = "an equality constraint (T extends int | string | boolean, or a string-literal enum) or a field constraint (T extends { readonly id: int; … })";

function readConstraint(p: TParam, fname: string, env: TypeEnv, used: Set<string>) {
  let c = p.decl.constraint;
  if (!c) return;
  while (ts.isParenthesizedTypeNode(c)) c = c.type;
  const what = `${p.name} extends ${c.getText()}`;
  const unsupported = (why: string): never => fail(c!, `the constraint ${what} is not supported: ${why}; VTS supports ${CONSTRAINT_FORMS}`);
  if (mentionsTypeParam(c, env.checker)) unsupported("it mentions a type parameter (constraints must be fixed types)");
  const K = ts.SyntaxKind;
  if (c.kind === K.UnknownKeyword || c.kind === K.AnyKeyword) unsupported("it constrains nothing (leave it out: an unconstrained type parameter is abstract)");
  if (c.kind === K.ObjectKeyword) unsupported("`object` says nothing about the fields (name the fields: T extends { readonly id: int })");
  if (ts.isTypeOperatorNode(c) && c.operator === K.KeyOfKeyword) unsupported("keyof is not supported");
  if (ts.isIntersectionTypeNode(c)) unsupported("intersections are not supported (an equality constraint and a field constraint cannot be combined)");
  if (ts.isConditionalTypeNode(c) || ts.isMappedTypeNode(c) || ts.isIndexedAccessTypeNode(c) || ts.isTypeQueryNode(c)) unsupported("conditional, mapped, indexed and typeof types are not supported");
  // a field constraint: an object type literal, or the name of a record type
  let fields: Field[] | null = null;
  if (ts.isTypeLiteralNode(c)) {
    // `T extends {}`: not nullish, which every instantiation is anyway
    if (c.members.length === 0) return;
    fields = [];
    for (const m of c.members) {
      if (!ts.isPropertySignature(m) || !m.type) fail(m, `the field constraint of ${p.name} may only list annotated fields (f: T or f?: T; no methods or index signatures)`);
      const f = m.name.getText();
      let ft = typeOfNode(m.type, env, capitalize(fname) + capitalize(p.name) + capitalize(f));
      if (m.questionToken && ft.k !== "opt") ft = T.opt(ft);
      fields.push({ name: f, type: ft });
    }
  } else if (ts.isTypeReferenceNode(c) && !env.isSpecInt(c)) {
    const t = typeOfNode(c, env, capitalize(fname) + capitalize(p.name));
    if (t.k === "rec") fields = env.reg.rec(t);
    else if (t.k === "union") unsupported(`${c.getText()} is a union of object types (constrain the fields its variants share: T extends { readonly f: … })`);
  }
  if (fields) {
    const ct = env.checker.getTypeFromTypeNode(c);
    p.fields = fields.map((f) => {
      if (f.type.k === "fn" || f.type.k === "node") fail(c!, `the field ${f.name} of the constraint of ${p.name} is not a value (functions and React nodes are not supported there)`);
      const base = `${p.name}_${f.name}`.replace(/[^A-Za-z0-9_$\u0080-\uffff]/g, "_");
      let acc = leanIdent(base);
      for (let k = 1; used.has(acc); k++) acc = leanIdent(`${base}_${k}`);
      used.add(acc);
      const sym = env.checker.getPropertyOfType(ct, f.name);
      if (sym) p.fieldTs.set(f.name, env.checker.getTypeOfSymbol(sym));
      return { name: f.name, type: f.type, acc };
    });
    return;
  }
  // an equality constraint: booleans, ints, strings, string literals and enums, or a union of them
  for (let m of ts.isUnionTypeNode(c) ? c.types : [c]) {
    while (ts.isParenthesizedTypeNode(m)) m = m.type;
    if (m.kind === K.NumberKeyword || (ts.isLiteralTypeNode(m) && ts.isNumericLiteral(m.literal))) {
      unsupported("number has no usable equality (NaN !== NaN, and SameValueZero equates -0 and 0): use int");
    }
    if (m.kind === K.NullKeyword || m.kind === K.UndefinedKeyword || (ts.isLiteralTypeNode(m) && m.literal.kind === K.NullKeyword)) {
      unsupported("a type parameter is never instantiated with null or undefined (write T | null where a value may be absent)");
    }
    if (m.kind === K.BooleanKeyword || m.kind === K.StringKeyword) continue;
    if (ts.isLiteralTypeNode(m) && (ts.isStringLiteral(m.literal) || m.literal.kind === K.TrueKeyword || m.literal.kind === K.FalseKeyword)) continue;
    if (ts.isTypeReferenceNode(m)) {
      if (env.isSpecInt(m)) continue;
      const t = typeOfNode(m, env, capitalize(fname) + capitalize(p.name));
      if (t.k === "num") unsupported(`${m.getText()} is number, which has no usable equality (NaN !== NaN, and SameValueZero equates -0 and 0): use int`);
      if (isEqType(t)) continue;
      unsupported(`${m.getText()} is ${showType(t)}, which JS does not compare by value (only booleans, ints, strings and enums are)`);
    }
    unsupported(`${m.getText()} is not a boolean, int, string or string-literal type`);
  }
  p.eq = true;
}

/** A type parameter inside an object type (a field's type): generic object types are not supported. */
function checkNoTVarField(t: VType, at: ts.Node) {
  if (!mentionsTVar(t)) return;
  const names = new Set<string>();
  const collectNames = (x: VType) => {
    if (x.k === "tvar") names.add(x.name);
    if (x.k === "arr" || x.k === "opt") collectNames(x.elem);
    if (x.k === "tuple") x.elems.forEach(collectNames);
  };
  collectNames(t);
  fail(at, `the type parameter ${[...names].join(", ")} appears inside an object type: generic object types are not supported in VTS (their Lean structure would depend on the type parameter); pass that value as a separate parameter of type ${[...names][0]}, or use a tuple [${[...names][0]}, …]`);
}

/** The declarations whose VTS type is being computed (a reference back to one is a recursive type). */
const inProgress = new Set<ts.Declaration>();

/** The VTS type denoted by a type alias / interface declaration. */
export function typeOfDecl(decl: ts.Declaration, env: TypeEnv): VType {
  const existing = env.reg.byDecl.get(decl);
  if (existing) return { k: existing.def.k, name: existing.qname } as VType;
  if (inProgress.has(decl)) fail(decl, `recursive types are not supported in VTS`);
  inProgress.add(decl);
  try {
    return typeOfDecl0(decl, env);
  } finally {
    inProgress.delete(decl);
  }
}

function typeOfDecl0(decl: ts.Declaration, env: TypeEnv): VType {
  const sf = decl.getSourceFile();
  if (ts.isInterfaceDeclaration(decl)) {
    if (decl.typeParameters?.length) fail(decl, "generic interfaces are not supported in VTS");
    if (decl.heritageClauses?.length) fail(decl, "interface inheritance is not supported in VTS; use a type alias");
    return recordFromMembers(decl.members, env, decl.name.text, decl, sf, decl);
  }
  if (ts.isTypeAliasDeclaration(decl)) {
    if (decl.typeParameters?.length) fail(decl, "generic type aliases are not supported in VTS");
    const name = decl.name.text;
    const t = decl.type;
    if (ts.isTypeLiteralNode(t)) return recordFromMembers(t.members, env, name, decl, sf, decl);
    if (ts.isUnionTypeNode(t)) return unionType(t, env, name, decl);
    if (ts.isLiteralTypeNode(t) && ts.isStringLiteral(t.literal)) return enumType([t.literal.text], env, name, decl, sf);
    // transparent alias (array, primitive, other alias)
    return typeOfNode(t, env, name);
  }
  fail(decl, `unsupported type declaration`);
}

function recordFromMembers(
  members: ts.NodeArray<ts.TypeElement>,
  env: TypeEnv,
  name: string,
  where: ts.Node,
  sf: ts.SourceFile,
  decl?: ts.Declaration,
): VType {
  const key = decl ?? where;
  const existing = env.reg.byDecl.get(key);
  if (existing) return { k: "rec", name: existing.qname };
  const fields: Field[] = [];
  const optional: boolean[] = [];
  for (const m of members) {
    if (!ts.isPropertySignature(m)) fail(m, "only property signatures are allowed in VTS object types (no methods/index signatures)");
    if (!m.type) fail(m, "properties need type annotations");
    const fname = m.name.getText();
    let ft = typeOfNode(m.type, env, name + capitalize(fname));
    checkNoTVarField(ft, m.type);
    if (m.questionToken && ft.k !== "opt") ft = T.opt(ft);
    fields.push({ name: fname, type: ft });
    optional.push(!!m.questionToken);
  }
  // an inline type literal: the same structure in this module is the same type
  let shape: string | null = null;
  if (!decl && ts.isTypeLiteralNode(where)) {
    const ck = env.checker;
    const objT = ck.getTypeFromTypeNode(where);
    const parts = fields.map((f, i) => {
      const ps = ck.getPropertyOfType(objT, f.name);
      const ns = ps ? nullShape(ck.getTypeOfSymbol(ps), f.type, ck) : null;
      return ns === null ? null : `${JSON.stringify(f.name)}${optional[i] ? "?" : ""}:${typeKey(f.type)}:${ns}`;
    });
    if (parts.every((x) => x !== null)) shape = `${env.nsOf(sf)}|rec|${parts.join(";")}`;
    const hit = shape ? env.reg.byShape.get(shape) : undefined;
    if (hit) {
      env.reg.byDecl.set(where, hit);
      return { k: "rec", name: hit.qname };
    }
  }
  const short = decl ? declTypeIdent(name, decl) : inlineTypeName(name, env, sf);
  const qname = `${env.nsOf(sf)}.${short}`;
  const nt: NamedType = { qname, short, module: env.nsOf(sf), def: { k: "rec", fields }, decl: key };
  env.reg.add(nt);
  if (shape) env.reg.byShape.set(shape, nt);
  return { k: "rec", name: qname };
}

/**
 * The Lean name of an inline type, after the hint `name` (e.g. `MkResult`): subscripted when
 * the name is taken (by another type, or by a type declared in the module), so that two
 * different inline types never share a name.
 */
function inlineTypeName(hint: string, env: TypeEnv, sf: ts.SourceFile): string {
  const ns = env.nsOf(sf);
  // (never of the shape of an instance name, see `declTypeIdent`)
  const name = INSTANCE_NAME_RE.test(hint) ? capitalize(hint) : hint;
  const declared = sf.statements.some((st) => (ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) && st.name.text === name);
  let short = leanIdent(name);
  for (let k = 2; declared || env.reg.byName.has(`${ns}.${short}`); k++) {
    short = leanIdent(subscripted(name, k));
    if (!env.reg.byName.has(`${ns}.${short}`)) break;
  }
  return short;
}

/**
 * The Lean name of a declared type.  Lean names the instances it derives for a type `T` (Lean
 * name) `inst<Class>T`, in the module namespace (`instReprP`, `instToJSList'` for a type `List`,
 * whose Lean name is `List'`): user values of that shape are renamed (`leanIdent`), and a type of
 * that shape is rejected (its own name, or its instances' names, could be another's).
 */
function declTypeIdent(name: string, decl: ts.Node): string {
  if (INSTANCE_NAME_RE.test(name)) {
    const at = (decl as ts.Node & { name?: ts.Node }).name ?? decl;
    fail(at, `the type name \`${name}\` is reserved in VTS: Lean names the instances it derives for a type T \`inst<Class>T\` (e.g. instReprList for a type List), so this type could clash with one; rename it`);
  }
  return leanIdent(name);
}

function enumType(lits: string[], env: TypeEnv, name: string, decl: ts.Declaration | undefined, sf: ts.SourceFile): VType {
  if (decl) {
    const existing = env.reg.byDecl.get(decl);
    if (existing) return { k: "enum", name: existing.qname };
    const short = declTypeIdent(name, decl);
    const qname = `${env.nsOf(sf)}.${short}`;
    env.reg.add({ qname, short, module: env.nsOf(sf), def: { k: "enum", lits }, decl });
    return { k: "enum", name: qname };
  }
  // an inline string-literal union: the same members in this module are the same type
  const shape = `${env.nsOf(sf)}|enum|${JSON.stringify([...new Set(lits)].sort())}`;
  const hit = env.reg.byShape.get(shape);
  if (hit) return { k: "enum", name: hit.qname };
  const short = inlineTypeName(name, env, sf);
  const nt: NamedType = { qname: `${env.nsOf(sf)}.${short}`, short, module: env.nsOf(sf), def: { k: "enum", lits } };
  env.reg.add(nt);
  env.reg.byShape.set(shape, nt);
  return { k: "enum", name: nt.qname };
}

function isNullish(n: ts.TypeNode): boolean {
  if (n.kind === ts.SyntaxKind.UndefinedKeyword || n.kind === ts.SyntaxKind.NullKeyword) return true;
  return ts.isLiteralTypeNode(n) && n.literal.kind === ts.SyntaxKind.NullKeyword;
}

function unionType(node: ts.UnionTypeNode, env: TypeEnv, name: string, decl: ts.Declaration | undefined): VType {
  const sf = node.getSourceFile();
  const members = node.types.filter((t) => !isNullish(t));
  const nullish = node.types.filter(isNullish);
  if (nullish.length > 1) fail(node, "a VTS type may include null or undefined, not both");
  if (nullish.length === 1) {
    if (members.length === 1) return T.opt(typeOfNode(members[0], env, name));
    const inner = ts.factory.createUnionTypeNode(members);
    // re-run on the non-null part (needs source positions for errors: use original node)
    return T.opt(unionOf(members, node, env, name, decl, sf));
  }
  return unionOf(members, node, env, name, decl, sf);
}

function unionOf(
  members: ts.TypeNode[],
  node: ts.Node,
  env: TypeEnv,
  name: string,
  decl: ts.Declaration | undefined,
  sf: ts.SourceFile,
): VType {
  // string literal union → enum
  if (members.every((m) => ts.isLiteralTypeNode(m) && ts.isStringLiteral(m.literal))) {
    const lits = members.map((m) => ((m as ts.LiteralTypeNode).literal as ts.StringLiteral).text);
    return enumType(lits, env, name, decl, sf);
  }
  // boolean = true | false
  if (members.length === 2 && members.every((m) => ts.isLiteralTypeNode(m) && (m.literal.kind === ts.SyntaxKind.TrueKeyword || m.literal.kind === ts.SyntaxKind.FalseKeyword))) {
    return T.bool;
  }
  // discriminated union of object types
  const objs: { members: ts.NodeArray<ts.TypeElement>; at: ts.Node }[] = [];
  for (const m of members) {
    if (ts.isTypeLiteralNode(m)) objs.push({ members: m.members, at: m });
    else if (ts.isTypeReferenceNode(m)) {
      let sym = env.checker.getSymbolAtLocation(m.typeName);
      if (sym && sym.flags & ts.SymbolFlags.Alias) sym = env.checker.getAliasedSymbol(sym);
      const d = sym?.declarations?.[0];
      if (d && ts.isTypeAliasDeclaration(d) && ts.isTypeLiteralNode(d.type)) objs.push({ members: d.type.members, at: d });
      else if (d && ts.isInterfaceDeclaration(d)) objs.push({ members: d.members, at: d });
      else fail(m, `union members must be object types with a common literal discriminant (or string literals)`);
    } else fail(m, `unsupported union member ${m.getText()}`);
  }
  if (objs.length === 1 && members.length === 1) return typeOfNode(members[0], env, name);
  // find the discriminant: a property present in every member with a string literal type
  const candidates = objs[0].members
    .filter((p): p is ts.PropertySignature => ts.isPropertySignature(p) && !!p.type && ts.isLiteralTypeNode(p.type) && ts.isStringLiteral(p.type.literal))
    .map((p) => p.name.getText());
  const tag = candidates.find((c) =>
    objs.every((o) => o.members.some((p) => ts.isPropertySignature(p) && p.name.getText() === c && p.type && ts.isLiteralTypeNode(p.type) && ts.isStringLiteral(p.type.literal))),
  );
  if (!tag) fail(node, `union of object types needs a common string-literal discriminant property (e.g. kind: "add")`);
  const short = decl ? declTypeIdent(name, decl) : leanIdent(INSTANCE_NAME_RE.test(name) ? capitalize(name) : name);
  const qname = `${env.nsOf(sf)}.${short}`;
  const key = decl ?? node;
  const existing = env.reg.byDecl.get(key);
  if (existing) return { k: "union", name: existing.qname };
  const variants: Variant[] = [];
  for (const o of objs) {
    const tagProp = o.members.find((p) => ts.isPropertySignature(p) && p.name.getText() === tag) as ts.PropertySignature;
    const lit = ((tagProp.type as ts.LiteralTypeNode).literal as ts.StringLiteral).text;
    if (variants.some((v) => v.lit === lit)) fail(o.at, `duplicate discriminant "${lit}"`);
    const fields: Field[] = [];
    for (const p of o.members) {
      if (!ts.isPropertySignature(p) || !p.type) fail(p, "only annotated property signatures allowed");
      const fname = p.name.getText();
      if (fname === tag) continue;
      let ft = typeOfNode(p.type, env, name + capitalize(lit) + capitalize(fname));
      checkNoTVarField(ft, p.type);
      if (p.questionToken && ft.k !== "opt") ft = T.opt(ft);
      fields.push({ name: fname, type: ft });
    }
    variants.push({ lit, ctor: lit, fields });
  }
  env.reg.add({ qname, short, module: env.nsOf(sf), def: { k: "union", tag, variants }, decl: key });
  return { k: "union", name: qname };
}
