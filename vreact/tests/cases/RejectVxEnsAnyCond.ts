// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | null`
// Through a conditional.
import { ensures, implies, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(xs: readonly int[], b: boolean): int | undefined {
  ensures((r) => implies(xs.length === 0 && b, isNull(b ? r : null)));
  return xs.find((x) => x > 0);
}
