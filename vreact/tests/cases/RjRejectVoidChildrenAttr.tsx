// expect: reject children={…} is not an attribute: React renders it as the element's children
// `children` given as an attribute is the element's children to React: on a void element such
// as <input> React throws while rendering it, and the app unmounts.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjVoidChildrenAttr() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      {n > 0 ? <input children="x" /> : <p>none</p>}
    </div>
  );
}
