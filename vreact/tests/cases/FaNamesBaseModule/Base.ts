// expect: verified verdict=verified total=verified prepend=verified errors=none
// PxLemmaUpstream with sums.ts named Base.ts: its lemma file cannot be proofs/Base.lean, the global
// lemma file every Defs.lean imports (an import cycle), so the module is VTS.Base_ and its lemmas
// are proofs/Base_.lean.
import { type int } from "vreact/spec";
export type Line = { readonly id: int; readonly cents: int };
/** @opaque */
export function total(xs: readonly Line[]): int {
  return xs.reduce((acc, l) => acc + l.cents, 0);
}
