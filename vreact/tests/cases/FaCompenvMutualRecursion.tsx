// expect: reject is called again while it runs
// Mutually recursive local functions: VTS inlines a local function where it is called, so it
// cannot be recursive (formerly "call to `g` is not supported (only … local helper arrows …)",
// false: `g` is one).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const f = (k: int): int => (k <= 0 ? 0 : g(k - 1));
  const g = (k: int): int => f(k);
  return <button onClick={() => setN(f(n))}>{n}</button>;
}
