// expect: reject a Map or Set the effect body mutates
// The timer callback sees the Map as the effect body left it ({1 → -5}), not as declared: a
// local Map / Set that the effect mutates is not bound in the callback (re-translating its
// declaration would give the empty Map, and `m.get(1) ?? 0` would be 0: VERIFIED, while JS sets
// n to -5).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const m = new Map<int, int>();
    m.set(1, -5);
    const id = setTimeout(() => setN(m.get(1) ?? 0), 100);
    return () => clearTimeout(id);
  }, []);
  return <p>{n}</p>;
}
