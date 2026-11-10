// expect: reject proofs/Base.lean:1:8: proofs/Base.lean is the global lemma file, imported by every generated Defs.lean, so it cannot import generated code: it imports VTS.m.Defs
// The global lemma file importing generated code under an escaped name (`«VTS».m.Defs` is the
// module VTS.m.Defs for Lean): vreact reads the imports as Lean's parser does, so this is the
// same import cycle as `import VTS.m.Defs`, reported at the import (not lake's raw cycle dump).
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
