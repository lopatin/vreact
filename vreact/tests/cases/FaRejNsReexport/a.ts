// expect: verified
// A namespace re-exported by another module (`export * as L from "./lib"`, imported by name)
// is lib's namespace too: `L.inc` is lib's inc.
import { type int, ensures } from "vreact/spec";
import { L } from "./mid";

export function f(x: int): int {
  ensures((r) => r === x + 1);
  return L.inc(x);
}
