// expect: reject `length` is not a field of the type parameter T
// T extends string is still abstract: no string properties or methods.
import { ensures, requires, type int } from "vreact/spec";

export function len<T extends string>(x: T): int {
  return x.length;
}
