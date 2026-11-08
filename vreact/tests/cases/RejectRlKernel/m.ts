// expect: reject proofs/m.lean:4:1: `set_option debug.skipKernelTC` is not allowed in a proof file ;; proofs/m.lean:8:3: `run_tac do ;; proofs/m.lean:9:41: `native_decide` is not allowed in a proof file: `native_decide` trusts compiled code ;; proofs/m.lean:10:50: `native` (e.g. `decide +native`) ;; proofs/m.lean:11:27: `by_elab ;; proofs/m.lean:12:29: `unsafe trivial` ;; proofs/m.lean:13:42: `Lean.ofReduceBool` ;; proofs/m.lean:14:31: `set_option debug.skipKernelTC` ;; proofs/m.lean:15:27: `set_option debug.skipKernelTC` ;; proofs/m.lean:16:1: `set_option trace.profiler` is not allowed ;; proofs/m.lean:17:1: `set_option trace.profiler.serve` is not allowed ;; trace.profiler.serve starts a web server and a browser ;; proofs/m.lean:18:1: `set_option trace.profiler.output` is not allowed ;; proofs/m.lean:19:48: `(config := ⟨false, true, true, false⟩)` is not allowed in a proof file: a configuration value can switch on native evaluation ;; proofs/m.lean:20:49: `(config := Lean.Parser.Tactic.DecideConfig.mk ;; proofs/m.lean:21:54: `bv_decide` is not allowed ;; proofs/m.lean:22:50: `bv_check "proof.lrat"` is not allowed
// User proofs that bypass Lean's kernel or trust compiled code (R4 item 12). Before the
// whitelist, proofs/m.lean's `bad` (a false lemma assigned `True.intro` by run_tac and added
// with debug.skipKernelTC, so no axiom shows it) made inc's false ensures VERIFIED. Every such
// command is rejected before Lean runs, with its file:line and text: options other than resource
// limits and output, run_tac/by_elab/unsafe code, native_decide/+native and Lean.ofReduceBool,
// also as `set_option … in` inside terms and tactics.
// Round 1: options are whitelisted by exact name — `trace.C` only for a trace class C — so
// `trace.profiler.serve` (Lean started a web server and the browser and waited) and
// `trace.profiler.output` (writes a file) are rejected (finding r4-lean-profiler-serve); a
// `decide` configuration value (`⟨false, true, true, false⟩` is +native: the proof was admitted as
// an axiom `pow10_eq._native.decide.ax_1_1`, finding r4-lean-native-config) and the bv_decide
// tactics of `grind =>` / `sym =>` (an external SAT solver) are rejected too.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 2);
  return x + 1;
}
