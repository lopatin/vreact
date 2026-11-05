import { ensures, type int } from "vreact/spec";
export function nextId(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
