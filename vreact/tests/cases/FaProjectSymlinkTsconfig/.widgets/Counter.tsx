// expect: reject src/Counter.tsx is a symbolic link (to .widgets/Counter.tsx): symbolic links in the source directory are not supported
// src/Counter.tsx is a link to src/.widgets/Counter.tsx, next to a tsconfig.json whose
// jsxImportSource is preact. VTS looked for the nearest tsconfig.json from the link's directory
// (the project's); Vite compiles the real file with the one next to it: its JSX calls preact's jsx.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < 3) setN(n + 1); }}>{n}</button>;
}
