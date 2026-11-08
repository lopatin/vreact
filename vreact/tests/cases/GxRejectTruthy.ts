// expect: reject truthiness of a value of the type parameter T is not supported
// Whether a T is truthy depends on the instantiation (0, "" and false are falsy): not a type mismatch.
import { type int } from "vreact/spec";

export function truthy<T>(x: T): int {
  return x ? 1 : 0;
}
