// expect: verified verdict=verified total=verified prepend=verified Cart=verified Cart.certificate=verified errors=none
// proofs/sums.lean proves facts about the @opaque total; prepend's ensures needs them (the exact
// v35-lemma2-fn repro, with a component). The lemmas import this module's Defs.lean, so they come
// after it; nothing else in the module calls prepend, so its ensures theorem is proved after the
// lemmas, in Posts.lean, and they help it (before: `postcondition of prepend` failed, since all
// ensures theorems were in Defs.lean). Cart, which needs the same lemma, is VERIFIED as well.
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
