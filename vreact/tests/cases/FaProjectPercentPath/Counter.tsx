// expect: reject src/limits%61.ts: its path ;; contains "%", which is not supported: the bundler's dev server (vite) serves a module at the URL of its path and percent-decodes the URL
// Vite's dev server rewrites "./limits%61" to the URL /src/limits%61.ts and percent-decodes the
// URL the browser asks for: it serves src/limitsa.ts (LIMIT = 100), not src/limits%61.ts, which
// TypeScript read (LIMIT = 3), and the invariant breaks on the 4th click (`vite build` bundles
// the right file; `npm run dev` does not).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./limits%61";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
