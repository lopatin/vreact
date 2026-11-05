// expect: reject onClick on <span> inside a submit button <button>
// A link handles a click on itself (it navigates), not one on its content: in Chromium
// the span's DOMActivate reaches the submit button first, which submits (n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
      <button><a href="#x"><span onClick={() => { if (n < 1) setN((m) => m + 1); }}>more</span></a></button>
    </form>
  );
}
