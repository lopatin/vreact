// expect: reject state updates during render are not allowed
// A setter in an array callback in the render is still the render-phase update.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function B() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const xs = [1].map((x) => { setN(x); return x; });
  return <p>{n + xs.length}</p>;
}
