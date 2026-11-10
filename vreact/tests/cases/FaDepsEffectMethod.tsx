// expect: reject `m.has` is a method, not a dependency
// An effect listing a method reference: rejected by the dependency check itself (before, only
// the dependency's translation refused it, as a function value).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsEffectMethod() {
  const [m, setM] = useState<ReadonlyMap<int, string>>(new Map<int, string>([[1, "a"]]));
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => { if (m.has(2)) setN((p) => p + 1); }, [m.has]);
  return <button type="button" onClick={() => setM(new Map<int, string>())}>{n}</button>;
}
