// expect: verified verdict=verified total=verified totalBoth=verified Totals=verified Totals.certificate=verified errors=none
// What the proof-file whitelist accepts (R4 item 12): proofs/sums.lean uses every allowed
// form — module doc, set_option of resource/linter options (as commands, `… in`, in terms and
// tactics), namespace/section/variable/end, private def, abbrev, example, theorem with
// @[vreact_simp]/@[simp]/@[grind =], attribute [local simp] and [-simp], grind_pattern, open
// … in, #check, #print, noncomputable section — and proofs/Base.lean (no imports) a generic
// lemma. The lemma total_append is what proves totalBoth's ensures and the component's
// invariant, so the files are really imported and used.
import { ensures, type int } from "vreact/spec";
import { total } from "./sums";
export function totalBoth(xs: readonly int[], ys: readonly int[]): int {
  ensures((r: int) => r === total(xs) + total(ys));
  return total(xs.concat(ys));
}
