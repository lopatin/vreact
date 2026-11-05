// expect: reject onClick on <span> inside a <label>
// A click on the span runs its onClick, then the label re-dispatches the click to its
// control (the checkbox): onChange runs in the same batch, from the same snapshot.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <label>
      <input type="checkbox" checked={n > 0} onChange={() => { if (n < 1) setN((m) => m + 1); }} />
      <span onClick={() => { if (n < 1) setN((m) => m + 1); }}>agree</span>
    </label>
  );
}
