// expect: reject onClick on a command button <button>
/// <reference path="./invokers.d.ts" />
// An invoker button runs a command on the element commandfor names: request-close fires
// `cancel` at the dialog synchronously, so onClick and the dialog's onCancel run in one
// batch (Chromium 152: one programmatic click leaves n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <button commandfor="d" command="request-close" onClick={() => { if (n < 1) setN((m) => m + 1); }}>close</button>
      <dialog id="d" open onCancel={() => { if (n < 1) setN((m) => m + 1); }}>dialog</dialog>
    </div>
  );
}
