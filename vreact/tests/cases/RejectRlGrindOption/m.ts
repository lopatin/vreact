// expect: reject proofs/m.lean:5:12: `set_option debug.skipKernelTC` is not allowed in a proof file ;; proofs/m.lean:10:12: `set_option trace.profiler.serve` is not allowed ;; proofs/m.lean:12:12: `set_option trace.profiler.output` is not allowed ;; proofs/m.lean:14:12: `set_option allowUnsafeReducibility` is not allowed
// An option set in grind's interactive mode (round-2 finding r4-lean-r2-grind-setoption): the
// whitelist checked the `set_option` of commands, terms and tactics only, while `grind =>
// set_option debug.skipKernelTC true in tactic => decide +kernel` (node kind
// `Lean.Parser.Tactic.Grind.setOption`) let `decide +kernel` add its theorem `decide False =
// true` without the kernel: `helper : False` had no axioms, and sq's false ensures was VERIFIED.
// Every node with the keyword `set_option` (any mode, also future ones) is now checked by its
// option name; a resource limit stays allowed there too (s4). The kernel re-check of the built
// modules is the backstop (RlSmuggledSkipKernel).
import { ensures, type int } from "vreact/spec";

// false: sq(0) is 0, not 1
export function sq(x: int): int {
  ensures((r: int) => r === x + 1);
  return x * x;
}
