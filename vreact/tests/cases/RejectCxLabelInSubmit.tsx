// expect: reject a <label> inside a submit button <button>
// No onClick anywhere: one programmatic click on the label submits the form twice in
// Chromium (the label's click, and the click it dispatches to its control, each
// activate the enclosing button): onSubmit runs twice from one snapshot, n = 2.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
      <button><label>name <input /></label></button>
    </form>
  );
}
