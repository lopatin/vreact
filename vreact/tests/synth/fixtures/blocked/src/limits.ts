import { requires, ensures, hole, type int } from "vreact/spec";

// a failing obligation (index without a bound check) in a function that capped uses:
// first's proof is `sorry`, so nothing that depends on first counts as proved
export function first(xs: readonly int[]): int {
  return xs[0];
}

export function capped(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  const y = first([x]);
  return hole<int>();
}

// an independent function in the same file is still checked (and can be proved)
export function low(x: int): int {
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
