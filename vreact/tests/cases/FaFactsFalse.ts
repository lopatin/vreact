// expect: fail fact index nonzero-divisor precondition
// Unfolding the @opaque constants of a fact (also in the obligations inside its statement)
// checks it by evaluation: a false fact, or one that indexes out of bounds, divides by zero
// or breaks a precondition, still fails.
import { assert, idiv, requires, type int } from "vreact/spec";

/** @opaque */
export const P: readonly int[] = [1, 2, 3];
/** @opaque */
export const Q: readonly int[] = [4, 5, 7];
/** @opaque */
export const Z: int = 0;

function at(xs: readonly int[], i: int): int {
  requires(0 <= i && i < xs.length);
  return xs[i];
}

assert(P[0] === 2);
assert(P.length === Q.length + 1);
assert(P[3] === 1 || P.length === 3);
assert(idiv(10, Z) === 0);
assert(at(Q, 3) === 3);
