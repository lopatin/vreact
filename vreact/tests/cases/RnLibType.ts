// expect: reject type Date (declared by a library
// A library's own type is not a VTS type (formerly read from its first declaration only).
import { type int } from "vreact/spec";

export function f(d: Date): int {
  return 1;
}
