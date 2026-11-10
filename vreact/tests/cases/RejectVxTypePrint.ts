// expect: reject type mismatch: expected readonly (number | null)[], got readonly (int | null)[]
// Union element types are printed in parentheses (an int | null is not widened to a number | null).
import { type int } from "vreact/spec";
export function f(xs: readonly (int | null)[]): readonly (number | null)[] {
  return xs;
}
