import { requires, ensures, hole, type int } from "vreact/spec";

// random arrays have at most 3 elements: the tests accept `a + b + 1` (and its reorderings), Lean rejects it
export function above(a: int, b: int, xs: readonly int[]): int {
  requires(a >= 0 && b >= 0);
  ensures((r: int) => r >= a + b + 1 && (r > a + b + 1 || xs.length < 4));
  return hole<int>();
}
