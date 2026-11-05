// expect: verified
// An unannotated ensures parameter (TypeScript `any`) may go where TypeScript would check its type
// when its value has the nullish kinds the type there says (the declared return type tells them),
// or once it is narrowed / defaulted.
import { ensures, implies, requires, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function isUndef(x: int | undefined): boolean {
  return x === undefined;
}
export function allNull(xs: readonly (int | null)[]): boolean {
  return xs.every((x) => x === null);
}
type R = { readonly v: int | null };
const UND: readonly (int | undefined)[] = [undefined];
export function f1(b: boolean): int | null {
  ensures((r) => implies(!b, isNull(r)));
  return b ? 1 : null;
}
export function f2(xs: readonly int[]): int | undefined {
  ensures((r) => implies(xs.length === 0, isUndef(r) && UND.includes(r)));
  return xs.find((x) => x > 0);
}
export function f3(n: int): readonly (int | null)[] {
  ensures((r) => allNull(r));
  return [null, null];
}
export function f4(b: boolean): R {
  ensures((r) => implies(!b, isNull(r.v)));
  return b ? { v: 1 } : { v: null };
}
export function f5(n: int): [int | undefined, int] {
  ensures((r) => isUndef(r[0]) && r[1] === n);
  return [undefined, n];
}
export function f6(xs: readonly int[]): int | undefined {
  requires(xs.length > 0 && xs[0] > 0);
  ensures((r) => !isNull(r!) && !isUndef(r ?? 1));
  return xs.find((x) => x > 0);
}
