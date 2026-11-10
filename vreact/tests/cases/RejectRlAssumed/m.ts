// expect: reject proofs/m.lean:4:57: `assumed` is not allowed in a proof file: `VReact.assumed` is the axiom behind the source's `assume(…)` facts ;; proofs/m.lean:5:41: `VReact.assumed` is not allowed ;; proofs/m.lean:6:42: `_root_.VReact.assumed` is not allowed ;; proofs/m.lean:7:50: `VReact.assumed` is not allowed ;; proofs/m.lean:8:22: `assumed` is not allowed ;; proofs/m.lean:9:14: `assumed` is not allowed ;; proofs/m.lean:10:18: `VReact.assumed` is not allowed
// A proof that uses the library's axiom `VReact.assumed` (round-2 finding r4-lean-r2-assumed): it
// proves anything, and the report said "ASSUMES … relies on unproved assume(…) facts" and
// "✔ VERIFIED modulo assume(…) facts" for sq, whose source has no assume(). The identifier is
// rejected in proof files in every spelling (qualified, `_root_`, `@`, `«…»`, in `open … (…)` and
// `renaming`, `attribute […]`); the kernel re-check is the backstop (RlSmuggledAssumed).
import { ensures, type int } from "vreact/spec";

// false: sq(0) is 0, not 1
export function sq(x: int): int {
  ensures((r: int) => r === x + 1);
  return x * x;
}
