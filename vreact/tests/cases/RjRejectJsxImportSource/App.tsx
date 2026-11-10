// expect: reject "jsxImportSource" must be "react" or absent
// The tsconfig's jsxImportSource makes every element the result of another library's jsx
// function (here a local runtime), while VTS models React's react/jsx-runtime.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjJsxImportSource() {
  const [n, setN] = useState<int>(0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
