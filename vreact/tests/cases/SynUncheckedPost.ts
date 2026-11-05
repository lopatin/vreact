// expect: fail index
// Why synth must not trust "no failure": with first() failing, capped's postcondition is never
// checked (only the index obligation is reported), although `return x` violates it for x = 21.
import { requires, ensures, type int } from "vreact/spec";

export function first(xs: readonly int[]): int {
  return xs[0];
}

export function capped(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return x;
}
