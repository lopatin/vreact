// expect: fail handler
// React batches setter calls and each `setX(v)` closes over the render snapshot:
// clicking runs `count := snap+1` twice, so count becomes odd. The model catches it.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function StaleBatch() {
  const [count, setCount] = useState<int>(0);
  invariant(count % 2 === 0);
  return <button onClick={() => { setCount(count + 1); setCount(count + 1); }}>{count}</button>;
}
