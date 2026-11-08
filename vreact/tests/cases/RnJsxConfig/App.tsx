// expect: reject tsconfig: VTS requires "jsx": "react-jsx"
// What JSX means is configured: with "preserve" (or the classic runtime, another
// jsxImportSource or a jsxFactory) the elements are compiled by another tool or call another
// factory, not React 18's automatic runtime, which is what VTS models.
import { useState } from "react";
import { type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  return <button type="button" onClick={() => setN(n + 1)}>{n}</button>;
}
