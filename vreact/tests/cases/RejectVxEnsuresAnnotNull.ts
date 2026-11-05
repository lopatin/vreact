// expect: reject is annotated `int | null` but receives a value of type `int | undefined`
// `ensures` takes `(result: any) => boolean`, so TypeScript never checks the annotation: here it
// says null where find() gives undefined, and `r === null` would be read as "absent" (in JS
// f([]) is undefined and the postcondition is false). The annotation must be the return type.
import { ensures, implies, type int } from "vreact/spec";
export function f(xs: readonly int[]): int | undefined {
  ensures((r: int | null) => implies(xs.length === 0, r === null));
  return xs.find((x) => x > 0);
}
