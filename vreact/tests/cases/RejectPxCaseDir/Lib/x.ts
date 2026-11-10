import { ensures, type int } from "vreact/spec";
import { clamp } from "../lib";
export function clamp2(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return clamp(x);
}
