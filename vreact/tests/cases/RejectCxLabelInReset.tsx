// expect: reject a <label> inside a reset button <button>
// As RejectCxLabelInSubmit, for a reset button: onReset runs twice (Chromium, n = 2).
// A label naming a control elsewhere (htmlFor) is rejected too (conservatively: with
// an onClick on that control, one click runs it and resets the form, n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <form onReset={() => { if (n < 1) setN((m) => m + 1); }}>
        <button type="reset"><label htmlFor="x">reset</label></button>
      </form>
      <input id="x" />
    </div>
  );
}
