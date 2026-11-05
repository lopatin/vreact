import ts from "typescript";
import { fail, leanField, leanIdent, leanStr, jsStr, capitalize } from "./util.ts";

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
  | { k: "fn"; params: Param[]; ret: VType };

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
  /** Per-module emission order. */
  order: NamedType[] = [];

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

export function sameType(a: VType, b: VType): boolean {
  if (a.k !== b.k) return false;
  switch (a.k) {
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
    default:
      return true;
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
      return `readonly ${showType(t.elem)}[]`;
    case "opt":
      return `${showType(t.elem)} | null`;
    case "tuple":
      return `[${t.elems.map(showType).join(", ")}]`;
    case "fn":
      return `(${t.params.map((p) => `${p.name}: ${showType(p.type)}`).join(", ")}) => ${showType(t.ret)}`;
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
  }
}

/** Whether Lean can derive `DecidableEq` (Floats and functions cannot). */
export function hasDecEq(t: VType, reg: TypeRegistry, seen = new Set<string>()): boolean {
  switch (t.k) {
    case "num":
    case "fn":
    case "node":
      return false;
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
    default:
      return true;
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
    const toJs = d.lits.map((l) => `    | .${leanField(l)} => ${jsStr(l)}`).join("\n");
    return (
      `inductive ${short} where\n${ctors}\n${deriv}\n\n` +
      `instance : VReact.JS.ToJS ${short} where\n  str := fun x => match x with\n${toJs}\n`
    );
  }
  // union
  const ctors = d.variants
    .map((v) => `  | ${leanField(v.ctor)}` + v.fields.map((f) => ` (${leanIdent(f.name)} : ${leanType(f.type)})`).join(""))
    .join("\n");
  let out = `inductive ${short} where\n${ctors}\n${deriv}\n`;
  // the discriminant as a string
  out += `\ndef ${short}.${leanField(d.tag)} : ${short} → VReact.JS.Str\n`;
  for (const v of d.variants) {
    out += `  | .${leanField(v.ctor)}${v.fields.map(() => " _").join("")} => ${jsStr(v.lit)}\n`;
  }
  // accessors for fields shared (same name & type) by all variants
  const shared = sharedFields(d.variants);
  for (const f of shared) {
    out += `\ndef ${short}.${leanField(f.name)} : ${short} → ${leanType(f.type)}\n`;
    for (const v of d.variants) {
      const pats = v.fields.map((g) => (g.name === f.name ? "x" : "_")).join(" ");
      out += `  | .${leanField(v.ctor)} ${pats} => x\n`;
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
  if (args.length) fail(node, `generic type ${name}<…> not supported in VTS`);
  return typeOfDecl(decl, env);
}

/** The VTS type denoted by a type alias / interface declaration. */
export function typeOfDecl(decl: ts.Declaration, env: TypeEnv): VType {
  const existing = env.reg.byDecl.get(decl);
  if (existing) return { k: existing.def.k, name: existing.qname } as VType;
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
  const qname = `${env.nsOf(sf)}.${leanIdent(name)}`;
  const key = decl ?? where;
  const existing = env.reg.byDecl.get(key);
  if (existing) return { k: "rec", name: existing.qname };
  // register first (fields filled below) so recursive references are detected
  const nt: NamedType = { qname, short: leanIdent(name), module: env.nsOf(sf), def: { k: "rec", fields: [] }, decl: key };
  const fields: Field[] = [];
  for (const m of members) {
    if (!ts.isPropertySignature(m)) fail(m, "only property signatures are allowed in VTS object types (no methods/index signatures)");
    if (!m.type) fail(m, "properties need type annotations");
    const fname = m.name.getText();
    let ft = typeOfNode(m.type, env, name + capitalize(fname));
    if (m.questionToken && ft.k !== "opt") ft = T.opt(ft);
    fields.push({ name: fname, type: ft });
  }
  nt.def = { k: "rec", fields };
  env.reg.add(nt);
  return { k: "rec", name: qname };
}

function enumType(lits: string[], env: TypeEnv, name: string, decl: ts.Declaration | undefined, sf: ts.SourceFile): VType {
  const qname = `${env.nsOf(sf)}.${leanIdent(name)}`;
  if (decl) {
    const existing = env.reg.byDecl.get(decl);
    if (existing) return { k: "enum", name: existing.qname };
  } else {
    const existing = env.reg.byName.get(qname);
    if (existing && existing.def.k === "enum" && existing.def.lits.join("|") === lits.join("|")) return { k: "enum", name: qname };
  }
  env.reg.add({ qname, short: leanIdent(name), module: env.nsOf(sf), def: { k: "enum", lits }, decl });
  return { k: "enum", name: qname };
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
  const qname = `${env.nsOf(sf)}.${leanIdent(name)}`;
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
      if (p.questionToken && ft.k !== "opt") ft = T.opt(ft);
      fields.push({ name: fname, type: ft });
    }
    variants.push({ lit, ctor: lit, fields });
  }
  // Constructor names live in the type's namespace next to the discriminant accessor
  // (`A.type`) and the shared-field accessors (`A.n`): a variant whose tag is one of those
  // names (`{ type: "type" }`) gets a primed constructor, as does one whose Lean name another
  // variant already has (`leanField` primes Lean's own auxiliary names: "rec" and "rec'").
  const d0 = (n: string): string => leanField(n).replace(/^«(.*)»$/, "$1");
  const taken = new Set([d0(tag), ...sharedFields(variants).map((f) => d0(f.name))]);
  for (const v of variants) {
    while (taken.has(d0(v.ctor))) v.ctor += "'";
    taken.add(d0(v.ctor));
  }
  env.reg.add({ qname, short: leanIdent(name), module: env.nsOf(sf), def: { k: "union", tag, variants }, decl: key });
  return { k: "union", name: qname };
}
