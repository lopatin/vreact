// expect: reject onClick on a submit button <input> (submitting its form runs onSubmit on <form>): one click runs both handlers
// A click on <input type="submit"> (or type="image") submits the form: dispatched by a
// script (el.click(), testing libraries), the submit event runs onSubmit before React
// renders onClick's update, so both handlers see n = 0 and n ends at 2 (react-dom 18.3.1).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onSubmit={(e) => { e.preventDefault(); if (n < 1) setN((m) => m + 1); }}>
      <input type="submit" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
    </form>
  );
}
