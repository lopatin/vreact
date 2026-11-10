import { ensures, type int } from "vreact/spec";
/** @trusted */
export function k(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
