// expect: reject module name clash
// limits.ts and limits.tsx would both become the Lean module VTS.limits: the generated Lean
// of one would silently replace the other (and `./limits` resolves to limits.ts).
import { ensures, type int } from "vreact/spec";
export function clampPct(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return x;
}
