// expect: reject proofs/Base.lean:2:8: proofs/Base.lean is the global lemma file, imported by every generated Defs.lean, so it cannot import generated code: it imports VTS.m.Defs
// The global lemma file importing generated code after a line comment that contains `/-` (and a
// later `-/`): Lean reads `/-` inside a line comment as part of the comment, so the import is
// real; vreact reads the imports as Lean's parser does and reports the import cycle at it.
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
