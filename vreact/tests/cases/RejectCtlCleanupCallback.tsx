// expect: reject effect cleanups may not update state or call parent callbacks
// The previous cleanup holds the previous render's onDone (a stale parent closure).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type ChildProps = { readonly onDone: () => void };
export function CtlChild(props: ChildProps) {
  useEffect(() => {
    return () => props.onDone();
  });
  return <span>child</span>;
}
export function CtlParent() {
  const [count, setCount] = useState<int>(0);
  invariant(0 <= count && count <= 1);
  return (
    <div>
      <button onClick={() => { if (count < 1) setCount((c) => c + 1); }}>{count}</button>
      <CtlChild onDone={() => { if (count < 1) setCount((c) => c + 1); }} />
    </div>
  );
}
