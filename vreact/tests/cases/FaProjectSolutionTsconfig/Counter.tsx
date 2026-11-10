// expect: reject tsconfig: "references" (a solution-style tsconfig.json, as in Vite's react-ts template) is not supported
// The layout of Vite's react-ts template: tsconfig.json has "references" to a tsconfig that
// includes the sources (here src/app/tsconfig.app.json, with jsxImportSource preact). Vite compiles
// a file tsconfig.json does not include with the referenced tsconfig that does: its JSX calls
// preact's jsx, while VTS checked it with tsconfig.json's settings (React).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < 3) setN(n + 1); }}>{n}</button>;
}
