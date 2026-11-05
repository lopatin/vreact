import { ensures, type int } from "vreact/spec";

export function at(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
