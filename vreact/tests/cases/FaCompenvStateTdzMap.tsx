// expect: reject reads `n`, which is declared after it
// An array callback runs in place, in the render: here before the useState whose value it reads
// (a ReferenceError in JS). Formerly VERIFIED: the state was bound for the whole body.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const xs: int[] = [1, 2].map((i) => i + n);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{xs.length}</button>;
}
