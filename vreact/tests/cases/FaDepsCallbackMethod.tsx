// expect: reject `m.has` is a method, not a dependency
// The useCallback sibling of FaDepsMemoMethod: React keeps the first closure (and its m) while
// `m.has` stays the same function; the model treats useCallback as a fresh closure.
import { useState, useCallback } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsCallbackMethod() {
  const [m, setM] = useState<ReadonlyMap<int, string>>(new Map<int, string>([[1, "a"], [2, "b"]]));
  const [sel, setSel] = useState<int>(1);
  const choose = useCallback(() => setSel(m.has(2) ? 2 : 1), [m.has]);
  invariant(m.has(1));
  invariant(m.has(sel));
  return (
    <div>
      <p>{m.get(sel)}</p>
      <button type="button" onClick={() => { setM(new Map<int, string>([[1, "a"]])); setSel(1); }}>drop</button>
      <button type="button" onClick={choose}>choose</button>
    </div>
  );
}
