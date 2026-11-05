// expect: reject onClick on <input> inside a reset button <button>
// A text field does not handle its click: in Chromium the enclosing reset button
// resets the form too (one programmatic click: onClick and onReset, n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onReset={() => { if (n < 1) setN((m) => m + 1); }}>
      <button type="reset"><input type="text" onClick={() => { if (n < 1) setN((m) => m + 1); }} /></button>
    </form>
  );
}
