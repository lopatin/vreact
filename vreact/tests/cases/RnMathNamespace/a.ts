// expect: reject `Math` here is not JavaScript's global Math
// A namespace import spelled `Math`: `Math.max(3, 1)` calls lib.max (3 - 1 = 2), not
// JavaScript's Math.max (formerly translated as Math.max, and `r === 3` was proved).
import { type int, ensures } from "vreact/spec";
import * as Math from "./lib";

export function h(): int {
  ensures((r) => r === 3);
  return Math.max(3, 1);
}
