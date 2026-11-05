// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `number | null`
// The callee from another module.
import { ensures, implies, type int } from "vreact/spec";
import { isNull } from "./util";
export function f(xs: readonly int[]): int | undefined {
  ensures((r) => implies(xs.length === 0, isNull(r)));
  return xs.find((x) => x > 0);
}
