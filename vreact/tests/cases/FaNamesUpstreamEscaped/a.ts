// expect: verified verdict=verified inca=verified twice=verified errors=none
// The lemma file of a.ts imports b.ts (which imports a.ts) under an escaped name, `«VTS».b.Defs`:
// vreact reads the imports as Lean's parser does, so it leaves the import of proofs/a.lean into b's
// Defs.lean out (it would close an import cycle), as for the plain `import VTS.b.Defs`.
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
