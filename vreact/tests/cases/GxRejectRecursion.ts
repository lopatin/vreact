// expect: reject recursion is not supported yet
// Generic functions may not recurse either.
import { ensures, requires, type int } from "vreact/spec";

export function len<T>(xs: readonly T[]): int {
  if (xs.length === 0) return 0;
  return 1 + len(xs.slice(1));
}
