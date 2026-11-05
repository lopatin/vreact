// expect: fail callback-rebased
// The callback a component with deferred updates implements for its child is
// rebased like its own discrete handlers: here an effect's setup sets `r`, so the
// snapshot-guarded shrink may be re-applied on top of it.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type Range = { readonly lo: int; readonly hi: int };
type ShrinkProps = { readonly onShrink: () => void };
export function Shrink(props: ShrinkProps) {
  return <button onClick={() => props.onShrink()}>-</button>;
}
export function Window() {
  const [r, setR] = useState<Range>({ lo: 0, hi: 10 });
  invariant(r.lo <= r.hi);
  useEffect(() => {
    setR((p) => (p.lo < p.hi ? { ...p, lo: p.lo + 1 } : p));
  }, [r.hi]);
  return <Shrink onShrink={() => { if (r.lo < r.hi) setR((p) => ({ ...p, hi: p.hi - 1 })); }} />;
}
