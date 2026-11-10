// expect: reject onClick on <label>: a click on a label
// label.click() runs onClick, then the label dispatches a second click to its control,
// which bubbles back through the label: onClick runs twice in one batch (n = 2 in
// react-dom 18.3.1 / jsdom, and in Chromium).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <label onClick={() => { if (n < 1) setN((m) => m + 1); }}>
      <input type="checkbox" /> agree
    </label>
  );
}
