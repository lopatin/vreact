// expect: verified verdict=verified f=verified proved=2 errors=none
// The inline type of the local `x` would be named `X`, which is the namespace of the nested module
// src/m/X.ts (VTS.m.X, with its function VTS.m.X.a, the type's field `a`): the type is named X₂
// (it was rejected as a name clash asking to rename a declaration `X` the module does not have).
import { ensures, type int } from "vreact/spec";
export function f(): int {
  ensures((r) => r === 1);
  const x: { readonly a: int } = { a: 1 };
  return x.a;
}
