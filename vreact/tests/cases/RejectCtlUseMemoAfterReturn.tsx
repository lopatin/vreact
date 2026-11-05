// expect: reject before any early return (Rules of Hooks)
// A hook after an early return: the number of hook calls changes between renders.
import { useState, useCallback } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlEarly() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  if (n === 1) {
    return <button onClick={() => setN(n + 1)}>one</button>;
  }
  const inc = useCallback(() => setN(n + 1), [n]);
  return <button onClick={inc}>{n}</button>;
}
