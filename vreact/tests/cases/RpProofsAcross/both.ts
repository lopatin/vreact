// expect: verified verdict=verified total=verified totalBoth=verified Totals=verified errors=none
// The lemma `total_append` in proofs/sums.lean (about module sums' @opaque function total)
// is needed by the ensures of totalBoth in *this* module: an importing module's Defs.lean
// must import Proofs.sums, not only VTS.sums.Defs (before: the postcondition failed, since
// function contracts are proved in Defs.lean, which saw only proofs/Base.lean).
import { ensures, type int } from "vreact/spec";
import { total } from "./sums";
export function totalBoth(xs: readonly int[], ys: readonly int[]): int {
  ensures((r: int) => r === total(xs) + total(ys));
  return total(xs.concat(ys));
}
