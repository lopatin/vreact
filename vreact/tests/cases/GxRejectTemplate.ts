// expect: reject converting to a string a value of the type parameter T
// ToString of a type parameter's value is not modelled.
import { ensures, requires, type int } from "vreact/spec";

export function show<T extends string>(x: T): string {
  return `<${x}>`;
}
