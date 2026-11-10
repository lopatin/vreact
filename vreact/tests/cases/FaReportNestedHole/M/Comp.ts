import { ensures, hole, type int } from "vreact/spec";
export function k(x: int): int {
  ensures((r: int) => r > x);
  return hole<int>();
}
