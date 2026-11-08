// expect: reject children of a <textarea> are its initial value to React
// React 18 throws while rendering a <textarea> with children and a defaultValue ("If you supply
// `defaultValue` on a <textarea>, do not pass children."), and with more than one child; with
// one child and no value, the child is the initial value, not an element.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjTextareaChildren() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      {n > 0 ? <textarea defaultValue="a">b</textarea> : <p>none</p>}
    </div>
  );
}
