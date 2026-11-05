import { requires, ensures, hole, type int } from "vreact/spec";

// an unrelated failing obligation (index without a bound check): the module's postconditions are not checked
export function first(xs: readonly int[]): int {
  return xs[0];
}

export function capped(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return hole<int>();
}

/** @trusted */
export function trustedCap(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return hole<int>();
}
