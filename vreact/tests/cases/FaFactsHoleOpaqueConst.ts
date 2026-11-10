// expect: status H=incomplete uncheckedwhy=hole()
// A fact about an @opaque constant whose value is a hole(): the obligations inside the fact
// unfold the constant, so a failure there is on the hole (blocked, not checked), not the
// fact's own.
import { assert, hole, type int } from "vreact/spec";

/** @opaque */
export const H: readonly int[] = hole<readonly int[]>();
assert(H[0] === 1);
