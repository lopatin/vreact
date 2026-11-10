// expect: fail handler
// The helper's update runs before the handler's own: `reset()` sets n to 0 and returns the old
// n + 1; the handler then sets n to that value, so n ends as old n + 1 — which breaks
// `n <= 3` at n = 3. (Were the helper's update applied after the handler's, n would end 0.)
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  const reset = (): int => {
    setN(0);
    return n + 1;
  };
  return <button onClick={() => { const v = reset(); setN(v); }}>{n}</button>;
}
