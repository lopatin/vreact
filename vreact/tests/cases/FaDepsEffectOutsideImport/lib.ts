import { ensures, type int } from "vreact/spec";

export const STEP: int = 2;

export function clampUp(p: int, d: int): int {
  ensures((r: int) => r >= 0);
  return p + d >= 0 ? p + d : 0;
}
