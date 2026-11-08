// expect: status verdict=not-verified errors=proof big=unchecked small=unchecked sum=unchecked keep=unchecked unchecked=4 proved=0
// No proof can compute or decide facts about numbers (R4 item 13). With Lean's `Float` the
// lemmas of proofs/m.lean were proved by `decide` (Lean has a computable model of Float, and
// its `max`/`min` are `maxOfLe`/`minOfLe`: `max 1 NaN = 1`, where Math.max(1, NaN) is NaN), and
// big's and small's false ensures were VERIFIED. Numbers are an opaque type with opaque
// operations now: `decide`, `rfl` and unfolding get nowhere: the lemmas are errors of the user
// proof (so nothing after them is checked: every item is UNCHECKED, the verdict NOT VERIFIED).
import { ensures, type int } from "vreact/spec";
export function big(): number {
  ensures((r: number) => r === 1);
  return Math.max(1, 0 / 0);
}
export function small(): boolean {
  ensures((r: boolean) => r === true);
  return Math.min(0 / 0, 1) === 1;
}
export function sum(): number {
  ensures((r: number) => r === 0.30000000000000004);
  return 0.1 + 0.2;
}
export function keep(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
