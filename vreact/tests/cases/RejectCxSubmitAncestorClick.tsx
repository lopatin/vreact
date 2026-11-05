// expect: reject is nested inside an element with onClick on <div>: one click runs both handlers
// The click on the submit button bubbles to the <div>'s onClick, then submits the form:
// both handlers in one batch, although the button itself has no handler.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onSubmit={(e) => { e.preventDefault(); if (n < 1) setN((m) => m + 1); }}>
      <div onClick={() => { if (n < 1) setN((m) => m + 1); }}>
        <button>go</button>
      </div>
    </form>
  );
}
