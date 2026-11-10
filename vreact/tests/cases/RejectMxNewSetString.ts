// expect: reject code points
import { type int } from "vreact/spec";

// new Set("ab") iterates code points, VTS strings are UTF-16 code units
export function letters(s: string): int {
  return new Set(s).size;
}
