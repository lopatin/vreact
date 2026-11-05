// expect: reject is annotated `int | undefined` but receives a value of type `int | null`
// The other nullish kind the other way round: the value is null, never undefined.
import { ensures, implies, type int } from "vreact/spec";
export function f(x: int | null): int | null {
  ensures((r: int | undefined) => implies(x === null, r === undefined));
  return x;
}
