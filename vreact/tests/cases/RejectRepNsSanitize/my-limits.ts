// expect: reject module name clash
// my-limits.ts and my_limits.ts both become the Lean module VTS.my_limits.
import { ensures, type int } from "vreact/spec";
export function clampPct(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return x;
}
