// expect: reject onClick on <button> inside a command button <button>
/// <reference path="./invokers.d.ts" />
// A nested button does not handle its click: in Chromium the enclosing invoker runs its
// command (request-close fires cancel at the dialog), so onClick and onCancel run in one
// batch (one programmatic click, n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <button commandfor="d" command="request-close"><button type="button" onClick={() => { if (n < 1) setN((m) => m + 1); }}>x</button></button>
      <dialog id="d" open onCancel={() => { if (n < 1) setN((m) => m + 1); }}>dialog</dialog>
    </div>
  );
}
