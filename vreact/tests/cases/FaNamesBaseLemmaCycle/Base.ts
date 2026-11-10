// expect: reject proofs/Base.lean:1:8: proofs/Base.lean is the global lemma file, imported by every generated Defs.lean, so it cannot import generated code: it imports VTS.Base.Defs ;; the lemmas about src/Base.ts (the Lean module VTS.Base_) go in proofs/Base_.lean
// A lemma file for src/Base.ts written as proofs/Base.lean: that is the global lemma file, which
// every Defs.lean imports, so its import of the module's Defs would be an import cycle (lake:
// "build cycle detected"); vreact says so, and where the module's lemmas go.
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
