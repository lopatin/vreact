// expect: reject onClick on <button> inside a submit button <button>
// Chromium dispatches DOMActivate at the click's target, and it bubbles to the
// enclosing submit button unless the target handles the click itself: a click on a
// nested type="button" runs its onClick and submits the form (Chromium 152, react-dom
// 18.3.1: one programmatic click leaves n = 2; jsdom follows the DOM spec, n = 1).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
      <button><button type="button" onClick={() => { if (n < 1) setN((m) => m + 1); }}>x</button></button>
    </form>
  );
}
