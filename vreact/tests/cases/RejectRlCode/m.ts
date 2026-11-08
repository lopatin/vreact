// expect: reject proofs/m.lean:3:1: `axiom cheat ;; an axiom is an unproved assumption ;; proofs/m.lean:4:1: `opaque oo : Nat` ;; proofs/m.lean:5:1: `#eval IO.FS.writeFile ;; running code while the proofs are checked ;; proofs/m.lean:6:1: `initialize pure ()` ;; proofs/m.lean:7:1: `run_cmd ;; proofs/m.lean:8:1: `structure St where` ;; proofs/m.lean:10:1: `partial` ;; proofs/m.lean:11:1: `mutual` ;; proofs/m.lean:15:20: `include_str ;; proofs/m.lean:17:1: `#exit`
// Axioms and code execution in a user proof (R4 item 12): an axiom made the items using it
// TRUSTED (the report catches it), `#eval`/`initialize`/`run_cmd` run arbitrary code while the
// proofs are checked (here: emptying a generated file, logging the evidence `vreact:ok`),
// `include_str` reads files; declarations other than theorem/def/abbrev/example are not needed
// for lemmas. All are rejected before Lean runs.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
