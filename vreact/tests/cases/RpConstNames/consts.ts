// expect: verified verdict=verified max=verified $lim=verified plain$=verified sumAll=verified errors=none
// Constants whose Lean names are escaped (`max'`, `«$lim»`) are reported under their
// TypeScript names, and their `#print axioms` lines name the generated constants (before:
// the escaped name was escaped again, `««$lim»»`, so Lean failed on the axiom report and a
// correct program was NOT VERIFIED).
import { assert, ensures, type int } from "vreact/spec";
/** @opaque */
export const max: int = 7;
assert(max > 0);
/** @opaque */
export const $lim: int = 3;
assert($lim > 1);
export const plain$: int = 2;
export function sumAll(x: int): int {
  ensures((r: int) => r === x + max + $lim + plain$ - max - $lim - plain$);
  return x;
}
