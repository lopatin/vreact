import { ensures, type int } from "vreact/spec";
export function clampPct(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return x < 0 ? 0 : x > 100 ? 100 : x;
}
