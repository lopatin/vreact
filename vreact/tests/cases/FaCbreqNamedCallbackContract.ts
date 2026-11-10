// expect: reject expected an inline arrow function
// A contract's every/some callback that is neither `(x) => condition` nor an inline function
// (here a module function) is left to the code reading, which rejects it, as it was rejected
// before (with "every((x) => condition) with an expression body").
import { requires, type int } from "vreact/spec";

function pos(x: int): boolean {
  return x > 0;
}

export function f(xs: readonly int[]): int {
  requires(xs.every(pos));
  return 0;
}
