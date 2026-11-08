// expect: reject default type arguments are not supported in VTS
// Default type arguments: callers write the type where it cannot be inferred.
import { ensures, requires, type int } from "vreact/spec";

export function empty<T = int>(): readonly T[] {
  return [];
}
