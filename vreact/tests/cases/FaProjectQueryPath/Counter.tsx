// expect: reject src/limits?v2.ts: its path ;; contains "?", which is not supported: the bundler (Vite) reads everything from the first "?" or "#" of a path as a URL query or hash
// The "?" variant of FaProjectHashPath: Vite cuts the path at its first "?" or "#":
// for "./limits?v2" it bundles src/limits.ts (LIMIT = 100), not src/limits?v2.ts, which
// TypeScript read (LIMIT = 3), and the invariant breaks on the 4th click.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./limits?v2";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
