// expect: fail effect-robust handler-rebased
// A timer callback captured in an effect closes over an old snapshot: `lo < hi` held
// when the effect ran, but `hi` may have been lowered since. Effects must be robust.
// The click is unsafe too: React 18 renders its `setHi(hi - 1)` first and later
// re-applies it after a pending timer `setLo(lo + 1)` (rebasing), giving lo > hi.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function StaleTimer() {
  const [lo, setLo] = useState<int>(0);
  const [hi, setHi] = useState<int>(10);
  invariant(lo <= hi);
  useEffect(() => {
    const id = setInterval(() => { if (lo < hi) setLo(lo + 1); }, 1000);
    return () => clearInterval(id);
  }, [lo, hi]);
  return <button onClick={() => { if (hi > lo) setHi(hi - 1); }}>{lo}..{hi}</button>;
}
