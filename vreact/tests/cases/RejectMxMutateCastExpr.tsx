// expect: reject (s as Map<int, int>).set(…) in an expression
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// the message shows the cast receiver in parentheses
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map());
  invariant(s.size === 0);
  return (
    <button
      onClick={() => {
        console.log((s as Map<int, int>).set(1, 1));
      }}
    >
      {s.size}
    </button>
  );
}
