// expect: reject Rules of Hooks
// One useMemo per branch: after `mode` flips, React returns the other branch's cached 100.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlSwap() {
  const [mode, setMode] = useState<boolean>(false);
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let cap: int = 0;
  if (mode) {
    const small = useMemo(() => 5, []);
    cap = small;
  } else {
    const big = useMemo(() => 100, []);
    cap = big;
  }
  return (
    <div>
      <button onClick={() => setMode(!mode)}>toggle</button>
      <span>{n + cap}</span>
    </div>
  );
}
