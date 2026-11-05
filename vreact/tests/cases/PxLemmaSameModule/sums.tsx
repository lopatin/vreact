// expect: fail postcondition verdict=not-verified total=verified prepend=incomplete Cart=verified Cart.certificate=verified failed=1 unchecked=0 errors=none
// proofs/sums.lean proves facts about the @opaque total. They come after this module's Defs.lean
// (they import it), so they help this module's components but not its own function contracts:
// prepend's ensures fails (a documented limitation: move such a function to a module that
// imports this one, see PxLemmaUpstream). The failure is a warning, so this module's View is
// still built and Cart, which needs the same lemma, is checked and VERIFIED (before: the failing
// prepend.post kept lake from building View.lean, and Cart was UNCHECKED).
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
export type Line = { readonly id: int; readonly cents: int };
/** @opaque */
export function total(xs: readonly Line[]): int {
  return xs.reduce((acc, l) => acc + l.cents, 0);
}
export function prepend(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + l.cents);
  return [l, ...xs];
}
export function Cart() {
  const [lines, setLines] = useState<readonly Line[]>([]);
  const [sum, setSum] = useState<int>(0);
  invariant(sum === total(lines));
  return <button onClick={() => { setLines([{ id: 1, cents: 5 }, ...lines]); setSum(sum + 5); }}>{sum}</button>;
}
