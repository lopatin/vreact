// expect: reject is not a module (it has no import or export)
// A source file without imports or exports is a script: TypeScript makes its declarations global
// and merges its interfaces with the libraries' (here the global `Math` gains a member).
import { type int } from "vreact/spec";

export function f(x: int): int {
  return Math.abs(x);
}
