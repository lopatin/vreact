import { requires, ensures, hole, type int } from "vreact/spec";

// synthesized through a path spelled in another letter case (SRC/limits.ts)
export function capped(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return hole<int>();
}
