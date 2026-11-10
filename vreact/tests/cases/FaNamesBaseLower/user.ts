import { ensures, type int } from "vreact/spec";
import { inca } from "./base";
export function thrice(x: int): int {
  ensures((r: int) => r > x);
  return inca(inca(inca(x)));
}
