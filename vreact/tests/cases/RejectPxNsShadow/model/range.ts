import { ensures, type int } from "vreact/spec";
export function bigger(a: int, b: int): int {
  ensures((r: int) => r >= a);
  return Math.max(a, b);
}
