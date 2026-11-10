// expect: verified A=verified K=verified at=verified first=verified
// A module-level fact is checked by evaluation, also the obligations inside its statement (an
// index, a divisor, a precondition): Lean elaborates them with the statement, before the
// proof unfolds the @opaque constant, so they unfold the constant themselves (formerly
// `assert(A[0] === 1)` failed its index obligation, `h : A.length ≤ 0 ⊢ False`, and the
// fact was not checked).
import { assert, ensures, idiv, requires, type int } from "vreact/spec";

/** @opaque */
export const A: readonly int[] = [1, 2, 3];
/** @opaque */
export const K: int = 3;

function at(xs: readonly int[], i: int): int {
  requires(0 <= i && i < xs.length);
  return xs[i];
}

assert(A[0] === 1);
assert(A.length === 3);
assert(idiv(10, K) === 3);
assert(at(A, 2) === 3);

// the facts are used where A is mentioned
export function first(): int {
  ensures((r) => r === 1);
  return A[0];
}
