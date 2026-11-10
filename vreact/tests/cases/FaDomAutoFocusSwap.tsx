// expect: reject onBlur on <input> with autoFocus updates state
// Two autoFocus elements that replace each other: each mount focuses the new one, whose onFocus
// (and the onBlur of the one it replaces, when that one is still in the page) updates n, which
// swaps them again, in nested commits until React throws "Maximum update depth exceeded". An
// update through a local closure counts.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Swap() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = () => setN((m) => m + 1);
  return n % 2 === 0 ? <input autoFocus onBlur={() => bump()} /> : <textarea autoFocus onFocus={bump} />;
}
