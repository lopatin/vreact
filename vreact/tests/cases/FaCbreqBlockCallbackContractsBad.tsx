// expect: fail precondition handler
// A block-bodied every in a requires or an invariant (read as code) is still checked: the call
// firstPos([0, 1]) breaks the precondition, and the handler appends -1, which breaks the invariant.
import { useState } from "react";
import { requires, invariant, type int } from "vreact/spec";

export function firstPos(xs: readonly int[]): int {
  requires(xs.length > 0 && xs.every((x) => { return x > 0; }));
  return xs[0];
}

export const ZERO: int = firstPos([0, 1]);

export function List() {
  const [xs, setXs] = useState<readonly int[]>([]);
  invariant(xs.every(function (x) { return x >= 0; }));
  return <button onClick={() => setXs([...xs, -1])}>{xs.length}</button>;
}
