// expect: reject a rest parameter `...xs` of the local function h is not supported
// A rest parameter collects the arguments into an array: h([]) has xs = [[]], length 1; the
// helper was inlined with xs bound to the argument [] (length 0), and `r === 0` proved.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 0);
  const h = (...xs: (readonly int[])[]): int => xs.length;
  return h([]);
}
