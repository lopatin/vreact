// expect: fail postcondition
/// <reference lib="es2023.array" />
// A comparator that is not consistent (cmp(a, b) = cmp(b, a) = 1): ECMA-262 leaves the
// order implementation-defined (V8 keeps [x, y], Lean's merge sort swaps), so the model
// must not let a proof rely on it. The bounds obligation (length) is still proved.
import { ensures, type int } from "vreact/spec";

export function firstAfterSort(x: int, y: int): int {
  ensures((r: int) => r === y);
  const ys = [x, y].toSorted((a: int, b: int) => 1);
  return ys[0];
}
