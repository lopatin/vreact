// expect: reject the type name `instFoo` is reserved in VTS
// Lean names the instances it derives for a type T `inst<Class>T`: a type of that shape could be,
// or have instances named like, another type's instance (formerly "has already been declared").
import { ensures, type int } from "vreact/spec";
type instFoo = { readonly x: int };
export function instReprInstFoo(): int {
  return 1;
}
export function f(p: instFoo): int {
  ensures((r: int) => r === p.x + 1);
  return p.x + instReprInstFoo();
}
