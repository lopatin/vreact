// expect: reject Rules of Hooks
// A hook inside for…of: the number of hook calls follows xs.length.
import { useState, useMemo } from "react";
import { type int } from "vreact/spec";
export function CtlInLoop() {
  const [xs, setXs] = useState<readonly int[]>([]);
  let total: int = 0;
  for (const x of xs) {
    const sq = useMemo(() => x * x, [x]);
    total = total + sq;
  }
  return <button onClick={() => setXs([...xs, 1])}>{total}</button>;
}
