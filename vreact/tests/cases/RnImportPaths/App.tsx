// expect: verified verdict=verified
// Relative imports that a bundler resolves to the file TypeScript reads: a directory's index
// ("./lib"), a full name ("./lib/index.ts", "./model.ts"), a `.js` path of a TypeScript file
// ("./steps.js" is steps.ts for Vite and TypeScript, steps.js not existing). A tsconfig "paths"
// entry that no VTS import uses is harmless: "react" and "vreact/spec" resolve to the same files
// without it.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { STEP } from "./lib";
import { BIG } from "./lib/index.ts";
import { MAX } from "./model.ts";
import { SMALL } from "./steps.js";

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= MAX);
  return (
    <div>
      <button onClick={() => setN(n + STEP <= MAX ? n + STEP : n)}>{n}</button>
      <button onClick={() => setN(n + BIG <= MAX ? n + BIG : n)}>big</button>
      <button onClick={() => setN(n + SMALL <= MAX ? n + SMALL : n)}>small</button>
    </div>
  );
}
