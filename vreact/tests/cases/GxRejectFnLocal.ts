// expect: reject `fs` has the function type (y: int) => int, which is not data
// A local whose annotated type contains a function (helper arrows themselves are inlined).
import { type int } from "vreact/spec";

export function count(): int {
  const fs: readonly ((y: int) => int)[] = [];
  return fs.length;
}
