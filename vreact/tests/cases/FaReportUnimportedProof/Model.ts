// expect: reject proofs/model.lean:1:1: no generated module imports the proof file proofs/model.lean (Lean module Proofs.model), so Lean would never check it ;; The lemmas of the module src/Model.ts go in proofs/Model.lean: the name must match in letter case ;; proofs/base.lean:1:1: no generated module imports the proof file proofs/base.lean ;; The file every module imports is proofs/Base.lean ;; proofs/Extra.lean:1:1: no generated module imports the proof file proofs/Extra.lean ;; proofs/sub/Helper.lean:1:1: no generated module imports the proof file proofs/sub/Helper.lean
// A proof file that no generated module imports, directly or through other proof files, is
// rejected (audit finding report-r1-3): lake builds only the root module VTS and its imports, so
// such a file was never elaborated — proofs/model.lean (a lowercase misspelling of
// proofs/Model.lean, the same file to most tools on a case-insensitive disk) with a `sorry` and
// a false theorem, and the report said VERIFIED, exit 0. Also proofs/base.lean (not Base.lean),
// and proofs/Extra.lean, which imports VTS.Model.Defs and proofs/sub/Helper.lean but is itself
// imported by nothing (so Helper is reached by nothing either).
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
