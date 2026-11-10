// expect: fail handler-rebased
// RxRebaseTimer with a parenthesized useState: the setter is still found to be called by the
// timer (a deferred source), so the click is checked when React rebases it onto the timer's
// pending update, and fails, as in the plain form.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type Range = { readonly lo: int; readonly hi: int };
export function Window() {
  const [r, setR] = (useState<Range>({ lo: 0, hi: 10 }));
  invariant(r.lo <= r.hi);
  (useEffect(() => {
    const id = setInterval(() => setR((p) => (p.lo < p.hi ? { ...p, lo: p.lo + 1 } : p)), 1000);
    return () => clearInterval(id);
  }, []));
  return <button onClick={() => { if (r.lo < r.hi) setR((p) => ({ ...p, hi: p.hi - 1 })); }}>{r.lo}..{r.hi}</button>;
}
