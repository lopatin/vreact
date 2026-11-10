// expect: verified A=verified B=verified diff=verified
// A module-level fact that mentions several @opaque constants unfolds every one of them, not
// only the constant it is attached to (formerly `assert(A.length === B.length)` unfolded only
// A and failed with `¬3 = B.length`, also after a fact about B stated above it).
import { assert, ensures, forall, type int } from "vreact/spec";

/** @opaque */
export const A: readonly int[] = [1, 2, 3];
/** @opaque */
export const B: readonly int[] = [4, 5, 6];

assert(B.length === 3);
assert(A.length === B.length);
assert(forall(0, A.length, (i) => A[i] < B[i]));

export function diff(): int {
  ensures((r) => r === 0);
  return A.length - B.length;
}
