// expect: reject this call has no modelled effect
// `console.log(…)` is an external write only when `console` is JavaScript's console: here it is a
// namespace import, and the call runs lib.log (whose precondition nothing checks) — formerly
// dropped as an external write.
import { type int, ensures } from "vreact/spec";
import * as console from "./lib";

export function h(xs: readonly int[]): int {
  ensures((r) => r === 1);
  console.log(xs);
  return 1;
}
