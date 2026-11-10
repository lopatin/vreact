// expect: verified
// The rebase-safe forms: guard inside the updater (the click) — and fields no
// deferred source writes keep the plain snapshot check (`count`: only clicks and a
// child callback write it, so React never rebases its updates).
import { useState, useEffect } from "react";
import { invariant, callbackRequires, type int } from "vreact/spec";
type Range = { readonly lo: int; readonly hi: int };
type StepProps = { readonly onStep: (by: int) => void };
export function Step(props: StepProps) {
  callbackRequires(props.onStep, (by) => by === 1);
  return <button onClick={() => props.onStep(1)}>+</button>;
}
export function Window() {
  const [r, setR] = useState<Range>({ lo: 0, hi: 10 });
  const [count, setCount] = useState<int>(0);
  invariant(r.lo <= r.hi);
  invariant(0 <= count && count <= 3);
  useEffect(() => {
    const id = setInterval(() => setR((p) => (p.lo < p.hi ? { ...p, lo: p.lo + 1 } : p)), 1000);
    return () => clearInterval(id);
  }, []);
  return (
    <div>
      <button onClick={() => setR((p) => (p.lo < p.hi ? { ...p, hi: p.hi - 1 } : p))}>{r.lo}..{r.hi}</button>
      <button onClick={() => { if (count < 3) setCount((c) => c + 1); }}>{count}</button>
      <Step onStep={(by) => { if (count + by <= 3) setCount(count + by); }} />
    </div>
  );
}
