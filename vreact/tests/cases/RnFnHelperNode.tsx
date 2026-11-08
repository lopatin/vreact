// expect: reject parameter `xs` of count has a React node (ReactNode / JSX.Element), which is not data
// React nodes are only rendered: a helper parameter of an array of nodes has no Lean value type
// (formerly an internal error, "node type has no Lean value type").
import { useState, type ReactNode } from "react";
import { type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  const count = (xs: readonly ReactNode[]): int => xs.length;
  return <button onClick={() => setN(n + 1)}>{count([])}</button>;
}
