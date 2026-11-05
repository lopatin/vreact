// expect: verified
// Functional updates see the queued state: two increments, count stays even.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function FunctionalBatch() {
  const [count, setCount] = useState<int>(0);
  invariant(count % 2 === 0);
  return <button onClick={() => { setCount((c) => c + 1); setCount((c) => c + 1); }}>{count}</button>;
}
