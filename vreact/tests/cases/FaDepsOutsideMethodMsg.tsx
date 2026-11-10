// expect: reject `Math.max` is a method, not a dependency: it is the same function for every receiver, so React never sees it change; a value from outside the component (`Math`) never needs listing
// A method of a global listed as a dependency: rejected (a method is never a data path), and the
// advice is no longer to list `Math`, which is not a value of the component, but to leave it out.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsOutsideMethodMsg() {
  const [n, setN] = useState<int>(0);
  const k: int = useMemo(() => Math.max(n, 1), [n, Math.max]);
  invariant(n >= 0);
  return <button type="button" onClick={() => setN(k)}>{n}</button>;
}
