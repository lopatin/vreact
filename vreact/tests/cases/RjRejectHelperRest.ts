// expect: reject a rest parameter `...xs` of the local function h is not supported
// A local helper is inlined with each parameter bound to the argument at its position; a rest
// parameter is the array of the remaining arguments instead.
import { ensures, type int } from "vreact/spec";

export function g(): int {
  ensures((r: int) => r === 0);
  const h = (...xs: readonly int[]): int => xs.length;
  return h();
}
