// expect: reject `get` reads `n`, which is declared after it
// A helper called in the render before the useState it reads: JS reads `n` in its temporal dead
// zone (React 18: "ReferenceError: Cannot access 'n' before initialization" at mount).
// TypeScript reports only direct reads (TS2448), not reads inside a function. Formerly VERIFIED:
// every state value was bound for the whole component body, declaration order ignored.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const get = (): int => n;
  const shown: int = get();
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{shown}</button>;
}
