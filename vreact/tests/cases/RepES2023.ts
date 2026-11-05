// expect: verified sortedCopy=verified setFirst=verified
// ES2023 change-array-by-copy methods type-check with the reference tsconfig (lib ES2023).
import { requires, type int } from "vreact/spec";
export function sortedCopy(xs: readonly int[]): readonly int[] {
  return xs.toSorted((a, b) => a - b).toReversed();
}
export function setFirst(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  return xs.with(0, v);
}
