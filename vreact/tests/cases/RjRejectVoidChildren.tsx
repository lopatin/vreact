// expect: reject <hr> is a void element: React throws while rendering it with children
// JSX children of a void element: React's assertValidProps throws ("hr is a void element tag
// and must neither have `children` …") once n > 0, and the app unmounts.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjVoidChildren() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      {n > 0 ? <hr>{n}</hr> : <p>none</p>}
    </div>
  );
}
