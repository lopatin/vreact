// expect: verified verdict=verified inca=verified twice=verified errors=none
// The lemma file of a.ts imports b.ts (which imports a.ts) after a line comment containing `/-`
// (and a later `-/`): Lean reads the import, and so does vreact, which leaves the import of
// proofs/a.lean into b's Defs.lean out (it would close an import cycle).
import { ensures, type int } from "vreact/spec";
export function inca(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
