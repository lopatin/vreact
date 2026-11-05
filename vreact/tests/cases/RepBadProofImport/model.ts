import { ensures, type int } from "vreact/spec";
export function twice(x: int): int {
  ensures((r: int) => r === x + x);
  return 2 * x;
}
