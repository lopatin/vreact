// expect: reject proofs/Helpers.lean:2:8: proofs/Base.lean is the global lemma file, imported by every generated Defs.lean, so it cannot import generated code: it imports VTS.m.Defs (through proofs/Helpers.lean)
// The global lemma file reaching generated code through another proof file: still an import
// cycle (every Defs.lean imports proofs/Base.lean), reported at the import.
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
