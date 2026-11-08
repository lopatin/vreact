// expect: status verdict=not-verified one=unchecked g=assumes errors=proof
// The attack the path in an assumed fact prevents: `if (flag) assume(flag)` is true whenever
// it runs, but with `VReact.assumed` at the fact alone Lean kept it as `g._proof_1 : ∀ flag,
// flag = true`, and a user proof derived False from it at `false` without naming the axiom —
// "proving" the false contract of `one` (JS: one(true) = 1), reported as relying on the
// program's assume(…) facts. Now `g._proof_1 false` needs `false = true`: the user proof does
// not elaborate (a user-proof error: NOT VERIFIED), and `one`'s postcondition, which comes after
// it, is not checked.
import { ensures, assume, type int } from "vreact/spec";

export function g(flag: boolean): int {
  if (flag) {
    assume(flag);
    return 1;
  }
  return 0;
}
export function one(x: boolean): int {
  ensures((r: int) => r === 2);
  return x ? 1 : 1;
}
