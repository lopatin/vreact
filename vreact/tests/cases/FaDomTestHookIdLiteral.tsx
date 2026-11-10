// expect: reject the global __VREACT_TEST__ (window.__VREACT_TEST__)
// runtime-r2-1: HTML's named access on Window makes globalThis.__VREACT_TEST__ this <div>;
// vreact/spec's runtime before the symbol key read its test hook there, and next(n) threw in
// the onClick. A written id that names a global the app's code reads (or starts with "_") is
// rejected; the runtime no longer reads a string-named global (FaDomTestHookId).
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

export function next(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div id="__VREACT_TEST__">
      <button onClick={() => setN(next(n))}>{n}</button>
    </div>
  );
}
