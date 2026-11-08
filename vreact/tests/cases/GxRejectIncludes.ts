// expect: reject includes on values of the type parameter T is not supported: T has no equality constraint
// includes compares with SameValueZero: only under an equality constraint.
import { ensures, requires, type int } from "vreact/spec";

export function has<T>(xs: readonly T[], x: T): boolean {
  return xs.includes(x);
}
