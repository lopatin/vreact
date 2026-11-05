// expect: verified
// Functional update over a single state record: robust against stale snapshots.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type Range = { readonly lo: int; readonly hi: int };
export function RobustTimer() {
  const [r, setR] = useState<Range>({ lo: 0, hi: 10 });
  invariant(r.lo <= r.hi);
  useEffect(() => {
    const id = setInterval(() => setR((p) => (p.lo < p.hi ? { ...p, lo: p.lo + 1 } : p)), 1000);
    return () => clearInterval(id);
  }, []);
  return <button onClick={() => { if (r.hi > r.lo) setR({ ...r, hi: r.hi - 1 }); }}>{r.lo}..{r.hi}</button>;
}
