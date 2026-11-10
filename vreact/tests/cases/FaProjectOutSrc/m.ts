// expect: reject "out" ("Src") is the same directory as the "src" directory
// "out" spelled like "src" in another letter case: the same directory on a case-insensitive disk.
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
