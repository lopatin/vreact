// expect: reject calling the method trim on a value of the type parameter T
// No string methods on a type parameter's values either.
import { ensures, requires, type int } from "vreact/spec";

export function trimmed<T extends string>(x: T): string {
  return x.trim();
}
