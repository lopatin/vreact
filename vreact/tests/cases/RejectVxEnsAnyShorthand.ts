// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | null`
// A shorthand field `{ r }` of a record whose field is `int | null`; also through a conditional and an array literal.
import { ensures, implies, type int } from "vreact/spec";
type P = { readonly r: int | null };
export function isNullP(p: P): boolean {
  return p.r === null;
}
export function f(xs: readonly int[]): int | undefined {
  ensures((r) => implies(xs.length === 0, isNullP({ r })));
  return xs.find((x) => x > 0);
}
