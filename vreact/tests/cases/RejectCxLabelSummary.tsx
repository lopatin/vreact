// expect: reject onClick on <summary> inside a <label>
// A <summary> outside a <details> is not interactive content to Chromium: the label
// re-dispatches the click to its control, whose onClick runs in the same batch (n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <label htmlFor="x"><summary onClick={() => { if (n < 1) setN((m) => m + 1); }}>s</summary></label>
      <input id="x" type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
    </div>
  );
}
