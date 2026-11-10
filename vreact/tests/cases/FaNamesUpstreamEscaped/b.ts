import { ensures, type int } from "vreact/spec";
import { inca } from "./a";
export function twice(x: int): int {
  ensures((r: int) => r > x);
  return inca(inca(x));
}
