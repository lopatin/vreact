// expect: fail postcondition dropKey=verified caller=incomplete
// An @opaque generic function is seen by its callers only through its contract: what it does not
// state (here: the length) is unknown at the call, although true in JS.
import { ensures, type int } from "vreact/spec";

/** @opaque */
export function dropKey<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => !r.includes(k));
  return xs.filter((x) => x !== k);
}

export function caller(xs: readonly int[]): int {
  ensures((r: int) => r <= xs.length);
  return dropKey(xs, 1).length;
}
