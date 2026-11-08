// expect: reject a timer's delay may not call `Array.prototype.push.call` here
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// Array.prototype.push.call(xs, 1): `.call` runs any function, here a mutator of the state array
export function ProtoCall() {
  const [xs, setXs] = useState<int[]>([]);
  invariant(xs.length === 0);
  useEffect(() => {
    const id = setTimeout(() => setXs([]), Array.prototype.push.call(xs, 1));
    return () => clearTimeout(id);
  }, [xs]);
  return <p>{xs.length}</p>;
}
