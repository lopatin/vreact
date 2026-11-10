// expect: reject new Map<…> has the function type (x: int) => int, which is not data
// A function type in a tuple Map value given as a type argument of `new Map` (it crashed the
// translator).
import { ensures, type int } from "vreact/spec";

export function h(): int {
  ensures((r) => r === 0);
  const m = new Map<int, readonly [int, (x: int) => int]>();
  return [...m.values()].length;
}
