// expect: fail handler-rebased
// The timer is robust, but the click's functional update is only safe from its
// snapshot: React 18 renders the click (SyncLane) before a pending timer update
// (DefaultLane), then replays both in order — f(u(s0)) = {lo: 10, hi: 9}.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type Range = { readonly lo: int; readonly hi: int };
export function Window() {
  const [r, setR] = useState<Range>({ lo: 0, hi: 10 });
  invariant(r.lo <= r.hi);
  useEffect(() => {
    const id = setInterval(() => setR((p) => (p.lo < p.hi ? { ...p, lo: p.lo + 1 } : p)), 1000);
    return () => clearInterval(id);
  }, []);
  return <button onClick={() => { if (r.lo < r.hi) setR((p) => ({ ...p, hi: p.hi - 1 })); }}>{r.lo}..{r.hi}</button>;
}
