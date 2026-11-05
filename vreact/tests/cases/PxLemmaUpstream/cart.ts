// expect: verified verdict=verified total=verified prepend=verified errors=none
// The function of PxLemmaSameModule whose contract needs the lemmas of proofs/sums.lean,
// moved to a module that imports sums: its Defs.lean imports Proofs.sums, so the lemmas help
// its ensures.
import { ensures } from "vreact/spec";
import { total, type Line } from "./sums";
export function prepend(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + l.cents);
  return [l, ...xs];
}
