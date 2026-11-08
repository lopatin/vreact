// expect: reject proofs/m.lean:4:1: `set_option debug.skipKernelTC` is not allowed in a proof file ;; proofs/m.lean:8:3: `run_tac do ;; proofs/m.lean:9:41: `native_decide` is not allowed in a proof file: `native_decide` trusts compiled code ;; proofs/m.lean:10:50: `native` (e.g. `decide +native`) ;; proofs/m.lean:11:27: `by_elab ;; proofs/m.lean:12:29: `unsafe trivial` ;; proofs/m.lean:13:42: `Lean.ofReduceBool` ;; proofs/m.lean:14:31: `set_option debug.skipKernelTC` ;; proofs/m.lean:15:27: `set_option debug.skipKernelTC`
// User proofs that bypass Lean's kernel or trust compiled code (R4 item 12). Before the
// whitelist, proofs/m.lean's `bad` (a false lemma assigned `True.intro` by run_tac and added
// with debug.skipKernelTC, so no axiom shows it) made inc's false ensures VERIFIED. Every such
// command is rejected before Lean runs, with its file:line and text: options other than resource
// limits and output, run_tac/by_elab/unsafe code, native_decide/+native and Lean.ofReduceBool,
// also as `set_option … in` inside terms and tactics.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 2);
  return x + 1;
}
