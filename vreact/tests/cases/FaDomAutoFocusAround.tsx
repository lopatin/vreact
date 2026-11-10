// expect: reject autoFocus on <input> inside an element with onFocus on <div>, which updates state
// focusin bubbles: the div's onFocus runs when the autoFocus input inside it is focused during
// the commit that mounts it, and its update remounts the input (new key), in nested commits until
// React throws "Maximum update depth exceeded". VERIFIED before.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Around() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div onFocus={() => setN((m) => m + 1)}>
      <span>{n}</span>
      <input key={n} autoFocus />
    </div>
  );
}
