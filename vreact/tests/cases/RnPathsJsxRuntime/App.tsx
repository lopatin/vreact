// expect: reject its JSX imports "react/jsx-runtime", which TypeScript resolves to
// The JSX of a "react-jsx" file imports "react/jsx-runtime" implicitly; tsconfig "paths" makes
// TypeScript check it against another library's JSX types (here: any attribute of any type),
// while the bundler loads React's runtime.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
