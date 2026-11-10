// expect: reject is read inside a functional update
// React calls a functional update when it processes it (and again on a rebase), after the
// event's dispatch: e.currentTarget is null then (TypeError), and e.target.value is the
// element's value at that time. The model would use the value of this event.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEventUpdater() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <input value={String(n)} onChange={(e) => setN((p) => p + (e.currentTarget.value === "x" ? 0 : 1))} />;
}
