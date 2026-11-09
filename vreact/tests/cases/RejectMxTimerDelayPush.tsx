// expect: reject a timer's delay may not call `xs.push` here (it mutates xs)
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// the delay is evaluated when the effect runs (not translated): xs.push(1) appends to the state
// array itself, which a later render shows
export function Delay() {
  const [xs, setXs] = useState<int[]>([]);
  const [k, setK] = useState(0);
  invariant(xs.length === 0 && k >= 0);
  useEffect(() => {
    const id = setTimeout(() => setXs([]), xs.push(1) * 1000000);
    return () => clearTimeout(id);
  }, [xs]);
  return <button onClick={() => setK(k + 1)}>{xs.length}</button>;
}
