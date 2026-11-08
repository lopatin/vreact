// expect: reject a command button <button> (commandfor/command
/// <reference types="invokers" />
// No onClick anywhere: a click on the nested invoker runs its command (onCancel) and,
// through DOMActivate, the enclosing submit button submits (onSubmit): Chromium 152,
// one programmatic click, n = 2.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
        <button><button type="button" commandfor="d" command="request-close">x</button></button>
      </form>
      <dialog id="d" open onCancel={() => { if (n < 1) setN((m) => m + 1); }}>dialog</dialog>
    </div>
  );
}
