import { ensures, type int } from "vreact/spec";

export function dec(x: int): int {
  ensures((r) => r < x);
  return x - 1;
}
