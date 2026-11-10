// expect: reject tsconfig: "extends": "./src/cfg/base" (in tsconfig.json) is not supported: TypeScript reads src/cfg/base.json, but the bundler (Vite's tsconfig loader, tsconfck
// TypeScript resolves "extends": "./src/cfg/base" to base.json (the path, then with ".json");
// Vite's tsconfck uses Node's require.resolve (the path, then .js, then .json) and reads
// base.js as the tsconfig: it compiles the JSX with jsxImportSource "/rt", a library vreact
// never saw (`import { jsx } from "/rt/jsx-runtime"`).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./limits";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
