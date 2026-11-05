// expect: reject parameter `x` is annotated `int | null` but receives a value of type `int | undefined`
// The same in a contract, through an unannotated ensures parameter (typed from the return type):
// the elements of r are undefined, never null.
import { ensures, type int } from "vreact/spec";
export function g(xs: readonly (int | undefined)[]): readonly (int | undefined)[] {
  ensures((r) => r.every((x: int | null) => x === null));
  return xs.filter((x) => x === undefined);
}
