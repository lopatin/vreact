// expect: reject proofs/x.y.lean:1:1: the proof file proofs/x.y.lean has no module name ;; proofs/my-lemmas.lean:1:1: the proof file proofs/my-lemmas.lean has no module name
// A proof file's path must be a Lean module name (attack on the fix of report-r1-3). vreact
// named proofs/x.y.lean and proofs/x/y.lean both `Proofs.x.y`, so `import Proofs.x.y` (which
// lake loads from x/y.lean) counted as an import of x.y.lean too: that file — a false `decide`
// theorem and a `sorry` — was never built, and the run said VERIFIED, exit 0. A directory or
// file name that is not an identifier (a `.`, a `-`, a space, a leading digit) is rejected.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
