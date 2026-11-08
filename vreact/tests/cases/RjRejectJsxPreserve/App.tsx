// expect: reject VTS requires "jsx": "react-jsx"
// With "jsx": "preserve" TypeScript leaves JSX to the bundler, whose own settings decide what an
// element means; VTS models TypeScript's react-jsx transform (React's automatic runtime).
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjJsxPreserve() {
  const [n, setN] = useState<int>(0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
