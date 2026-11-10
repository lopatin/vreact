// expect: reject `m.has` is a method, not a dependency
// A method reference as a useMemo dependency: `m.has` is Map.prototype.has, the same function for
// every Map, so React's Object.is never sees it change and keeps the first value (pick = 2 after
// "drop" makes m = {1}; "choose" then sets sel = 2 and breaks m.has(sel)). The model recomputes
// the memo at every render, so the dependency check must not let `m.has` cover `m.has(2)`.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsMemoMethod() {
  const [m, setM] = useState<ReadonlyMap<int, string>>(new Map<int, string>([[1, "a"], [2, "b"]]));
  const [sel, setSel] = useState<int>(1);
  const pick: int = useMemo(() => (m.has(2) ? 2 : 1), [m.has]);
  invariant(m.has(1));
  invariant(m.has(sel));
  return (
    <div>
      <p>{m.get(sel)}</p>
      <button type="button" onClick={() => { setM(new Map<int, string>([[1, "a"]])); setSel(1); }}>drop</button>
      <button type="button" onClick={() => setSel(pick)}>choose</button>
    </div>
  );
}
