// expect: reject node_modules/gen/VTS/KEEP.txt is not a file vreact generated
// "out" is a directory that already holds a file of the user in VTS/: vreact removes nothing
// but the Lean files it generated.
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
