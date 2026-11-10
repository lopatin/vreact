// expect: reject onFocus on <input> with autoFocus updates state
// effects-r2-2: React focuses the autoFocus input in the commit that mounts it; onFocus runs
// inside that commit, its update is rendered and committed at once, and the new key mounts a new
// autoFocus input, which is focused again: after 50 nested commits setN throws "Maximum update
// depth exceeded" inside the handler. VERIFIED before.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Chain() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <input key={n} type="text" autoFocus onFocus={() => setN((m) => m + 1)} />;
}
