// expect: verified
// An "extends" path that TypeScript and Vite's tsconfck resolve to the same file (the file named
// in full, ending in .json) is accepted.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./limits";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
