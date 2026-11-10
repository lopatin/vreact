// expect: reject the useMemo function runs here, at the call, and reads `step`, declared after it
// The useMemo function runs at the call, before `const step` has run: a ReferenceError in JS
// (TypeScript does not flag a read inside a function). Rejected with that reason.
import { useState, useMemo } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const next = useMemo(() => n + step, [n]);
  const step: int = 2;
  return <button onClick={() => setN(next)}>{n}</button>;
}
