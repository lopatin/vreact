// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | null`
// includes compares with SameValueZero: [null].includes(undefined) is false in JS.
import { ensures, implies, type int } from "vreact/spec";
const NULLS: readonly (int | null)[] = [null];
export function f(xs: readonly int[]): int | undefined {
  ensures((r) => implies(xs.length === 0, NULLS.includes(r)));
  return xs.find((x) => x > 0);
}
