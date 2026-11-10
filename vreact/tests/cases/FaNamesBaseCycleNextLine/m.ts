// expect: reject proofs/Base.lean:2:3: proofs/Base.lean is the global lemma file, imported by every generated Defs.lean, so it cannot import generated code: it imports VTS.m.Defs
// The global lemma file importing generated code with the module name on the line after
// `import`: the import cycle is reported where the module name is (it was reported at 0:0).
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
