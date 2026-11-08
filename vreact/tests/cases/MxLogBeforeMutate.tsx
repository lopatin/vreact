// expect: verified
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

// Logging or writing out a fresh Map / Set before mutating it leaves no alias the model reads:
// console.*, localStorage.setItem and document.title print or convert the value when they run.
export function build(xs: readonly int[]): int {
  ensures((r) => r >= 0 && r <= xs.length);
  const n = new Map<int, int>();
  console.log("start", n);
  localStorage.setItem("n", JSON.stringify(n));
  for (const x of xs) n.set(x, x);
  console.log("done", n);
  return n.size;
}

export function MxLogBeforeMutate() {
  const [sel, setSel] = useState<ReadonlySet<int>>(new Set());
  invariant(sel.size <= 3);
  return (
    <button
      onClick={() =>
        setSel((s) => {
          const next = new Set(s);
          console.log("before", next, JSON.stringify([...next], null, 2));
          document.title = JSON.stringify(next);
          if (next.has(1)) next.delete(1);
          else if (next.size < 3) next.add(1);
          return next;
        })
      }
    >
      {sel.size}
    </button>
  );
}
