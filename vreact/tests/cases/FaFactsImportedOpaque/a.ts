// expect: verified Y=verified
// A fact about this module's @opaque constant Y that also mentions X, an @opaque constant of
// an imported module, unfolds X too, also in the index obligations inside it: the fact is
// checked by evaluation (formerly both index obligations failed, Y and X folded, and the
// fact's proof unfolded only Y).
import { assert, type int } from "vreact/spec";
import { X } from "./consts";

/** @opaque */
export const Y: readonly int[] = [5, 6];

assert(Y.length === X.length && Y[1] === X[0] + 4);
