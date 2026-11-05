// expect: reject onClick on a reset button <button> (resetting its form runs onReset on <form>): one click runs both handlers
// A reset button's click fires `reset` at its form in the same batch (react-dom 18.3.1:
// one programmatic click leaves n = 2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <form onReset={() => { if (n < 1) setN((m) => m + 1); }}>
      <button type="reset" onClick={() => { if (n < 1) setN((m) => m + 1); }}>reset</button>
    </form>
  );
}
