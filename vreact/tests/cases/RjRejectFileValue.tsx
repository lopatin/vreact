// expect: reject defaultValue on an <input> that is type="file"
// React sets input.value = "x" when it mounts the element, which throws an InvalidStateError on
// a file input (its value can only be set to ""), and the app unmounts.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjFileValue() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      {n > 0 ? <input type="file" defaultValue="x" /> : <p>none</p>}
    </div>
  );
}
