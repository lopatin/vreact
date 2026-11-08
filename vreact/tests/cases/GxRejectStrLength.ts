// expect: reject `length` on a value of the type parameter T is not supported: under an equality constraint
// T extends string is still abstract: no string properties or methods.
import { ensures, requires, type int } from "vreact/spec";

export function len<T extends string>(x: T): int {
  return x.length;
}
