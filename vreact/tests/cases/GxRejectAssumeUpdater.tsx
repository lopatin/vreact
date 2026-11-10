// expect: reject assume(…) is not supported in a functional update
// A functional update is a Lean function of any state (React may apply it to a state other
// than the snapshot), so this assume(…) would be the theorem `∀ n, n < 5` — false, although
// the invariant and the guard make it true for every state the handler sees.
import { useState } from "react";
import { assume, invariant, type int } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n <= 5);
  return (
    <button
      onClick={() => {
        if (n < 5) {
          setN((p) => {
            assume(p < 5);
            return p + 1;
          });
        }
      }}
    >
      {n}
    </button>
  );
}
