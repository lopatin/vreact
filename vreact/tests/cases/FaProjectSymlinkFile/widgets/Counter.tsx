// expect: reject src/Counter.tsx is a symbolic link (to widgets/Counter.tsx): symbolic links in the source directory are not supported
// src/Counter.tsx is a link to src/widgets/Counter.tsx (whose files vreact.json excludes).
// TypeScript resolves "./model" from the link's directory (src/model.ts, LIMIT = 3); Vite gives
// the module its real path and resolves from there: src/widgets/model.ts (LIMIT = 100), and the
// invariant breaks on the 4th click.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./model";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
