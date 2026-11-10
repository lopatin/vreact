// expect: fail handler
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// wrong: the handler's copy is named `console`; `console.add(1)` adds to the copy, which becomes
// the state, so the state Set does not stay empty
export function MxConsoleLocalHandler() {
  const [sel, setSel] = useState(new Set<int>());
  invariant(sel.size === 0);
  return (
    <button
      onClick={() => {
        const console = new Set(sel);
        console.add(1);
        setSel(console);
      }}
    >
      {sel.size}
    </button>
  );
}
