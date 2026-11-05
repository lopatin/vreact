import ts from "typescript";
import path from "node:path";
import { Program } from "../../src/ctx.ts";
import { typeOfNode, T } from "../../src/types.ts";
import { Enumerator } from "../../src/synth.ts";
const f = path.resolve("src/cart.ts");
const program = ts.createProgram([f], { strict: true, jsx: ts.JsxEmit.ReactJSX, moduleResolution: ts.ModuleResolutionKind.Bundler, module: ts.ModuleKind.ESNext });
const prog = new Program(program.getTypeChecker(), process.cwd(), () => "VTS.cart");
const sf = program.getSourceFile(f)!;
let cart: any;
for (const st of sf.statements) if (ts.isTypeAliasDeclaration(st)) { const t = typeOfNode(ts.factory.createTypeReferenceNode(st.name), prog.typeEnv, st.name.text); if (st.name.text === "Cart") cart = t; }
const it = { k: "rec", name: "VTS.cart.Item" } as any;
const scope = [{ code: "c", type: cart, size: 1 }, { code: "c.items", type: T.arr(it), size: 1 }, { code: "c.nextId", type: T.int, size: 1 }, { code: "id", type: T.int, size: 1 }];
const en = new Enumerator(prog, scope, cart, 9);
for (let s = 1; s <= 6; s++) { const ts_ = en.terms(cart, s); console.log(s, ts_.length, ts_.slice(0, 6).map((a) => a.code)); }
console.log("arr size 4:", en.terms(T.arr(it), 4).slice(0, 5).map((a) => a.code));
