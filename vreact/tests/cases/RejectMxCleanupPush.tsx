// expect: reject effect cleanups may not call `xs.push` here (it mutates xs)
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// a cleanup's console.log argument (not translated) appends to the state array
export function Cleanup() {
  const [xs, setXs] = useState<int[]>([]);
  invariant(xs.length === 0);
  useEffect(() => {
    return () => {
      console.log(xs.push(1));
    };
  }, [xs]);
  return <button onClick={() => setXs([])}>{xs.length}</button>;
}
