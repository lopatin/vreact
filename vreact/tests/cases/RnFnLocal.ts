// expect: reject `fs` has the function type () => void, which is not data
// A local array of functions (formerly an internal error), and a hole of a function type.
import { type int } from "vreact/spec";

export function f(x: int): int {
  const fs: readonly (() => void)[] = [];
  return x + fs.length;
}
