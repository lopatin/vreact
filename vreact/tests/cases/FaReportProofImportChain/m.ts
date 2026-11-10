// expect: verified verdict=verified total=verified errors=none
// A proof file that a module's own proof file imports is reached from the generated modules and
// checked (the positive side of FaReportUnimportedProof): proofs/m.lean imports
// proofs/lemmas/Sums.lean, whose lemma proves total's ensures.
import { ensures, type int } from "vreact/spec";
/** @opaque */
export function sum(xs: readonly int[]): int {
  return xs.reduce((a, b) => a + b, 0);
}
export function total(xs: readonly int[], ys: readonly int[]): int {
  ensures((r: int) => r === sum(xs) + sum(ys));
  return sum([...xs, ...ys]);
}
