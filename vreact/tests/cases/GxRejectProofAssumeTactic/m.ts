// expect: reject proofs/m.lean:6:60: `vreact_assume` is not allowed in a proof file: `vreact_assume` is the translator's proof of the source's `assume(…)` facts
// `vreact_assume` (VReact/Assumed.lean) is the tactic the translator writes for an assume(…):
// it applies the axiom `VReact.assumed`, which proves anything. A proof file that uses it
// would state an unproved fact without naming the axiom, so the whitelist rejects the tactic
// like the identifier `assumed` (RejectRlAssumed); the kernel re-check and the
// `#vreact_assumed` audit are further lines of defence (GxAssumeInProofs).
import { ensures, type int } from "vreact/spec";

// false: sq(0) is 0, not 1
export function sq(x: int): int {
  ensures((r: int) => r === x + 1);
  return x * x;
}
