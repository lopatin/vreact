import { ensures, type int } from "vreact/spec";
import { first } from "./model";
export function nextPos2(x: int): int {
  ensures((r: int) => r > x);
  return first([x + 1]);
}
