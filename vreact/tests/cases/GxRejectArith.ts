// expect: reject arithmetic (+) on a value of the type parameter T is not supported: its values are abstract
// Values of a type parameter are abstract, even with an equality constraint T extends int.
import { ensures, requires, type int } from "vreact/spec";

export function inc<T extends int>(x: T): int {
  return x + 1;
}
