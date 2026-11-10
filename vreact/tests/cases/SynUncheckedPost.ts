// expect: fail index postcondition
// A failure in one function (first) must not hide another's: capped's postcondition is still
// checked (it is emitted right after capped in Defs.lean) and fails, since `return x` violates it
// for x = 21. (Synth must not trust "no failure" when a declaration was not elaborated.)
import { requires, ensures, type int } from "vreact/spec";

export function first(xs: readonly int[]): int {
  return xs[0];
}

export function capped(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return x;
}
