// expect: reject the initialiser of `A` calls `g`, which calls `k`, which reads `A` (itself)
// A constant read (transitively, through two calls) by its own initialiser is still in its
// temporal dead zone.
import { type int } from "vreact/spec";

function k(): int {
  return A + 1;
}
function g(): int {
  return k();
}
export const A: int = [1, 2].map((x) => x + g())[0];
