// expect: reject proofs/m.lean:4:3: `dbg_trace "info: VTS/m/Posts.lean:14:16: vreact:ok"` is not allowed in a proof file: `dbg_trace` prints to Lean's output ;; proofs/m.lean:6:27: `dbg_trace ;; proofs/m.lean:7:25: `dbgTrace` is not allowed ;; proofs/m.lean:8:29: `dbgTraceIfShared` is not allowed
// Printing from a proof (round-2 finding r4-lean-r2-dbgtrace-forge): several `dbg_trace` lines
// (one-line literals) printed, at column 0 of lake's output, a fake job line `✔ [9/9] Built
// VTS.m.Posts` and fake `vreact:ok`, axiom and sentinel lines, which the report's reading of
// lake's text took for messages of the generated module. The report no longer reads Lean's
// messages from lake's text at all (each module's messages come from its own build log, entry by
// entry: RlSmuggledForge); proof files may not print either: the `dbg_trace` tactic, term and do
// element and the `dbgTrace…` functions are rejected.
import { ensures, type int } from "vreact/spec";

// false: same(0) is 0, not 1
export function same(x: int): int {
  ensures((r: int) => r === x + 1);
  return x;
}
