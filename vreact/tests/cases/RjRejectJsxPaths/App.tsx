// expect: reject its JSX calls react/jsx-runtime, which resolves to src/rt/jsx-runtime.d.ts, not to React's
// tsconfig "paths" maps react/jsx-runtime, which every element of a react-jsx file calls, to a
// file of the project (esbuild and bundler plugins honour "paths" too): JSX would be that
// file's jsx function, not React's.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjJsxPaths() {
  const [n, setN] = useState<int>(0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
