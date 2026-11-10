// expect: reject a functional update `setX((prev) => …)` may not update state
// A setter inside a functional update in a handler: React calls the updater while it computes
// the next state, so this is rejected for that reason (not as an update "during render" that
// should move into a handler).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function B() {
  const [n, setN] = useState<int>(0);
  const [k, setK] = useState<int>(0);
  invariant(n >= 0 && k >= 0);
  return <button onClick={() => setN((m) => { setK(1); return m + 1; })}>{n}</button>;
}
