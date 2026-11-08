// expect: reject cannot infer the type parameter T of emptyOf from the arguments
// A type parameter that occurs only in the result needs explicit type arguments (or a result type).
import { ensures, requires, type int } from "vreact/spec";

export function emptyOf<T>(): readonly T[] {
  return [];
}
export function g(): int {
  const xs = emptyOf();
  return xs.length;
}
