// expect: verified
// for…of with local mutation translates to a fold; total is shown, nothing to prove.
import { useState } from "react";
import { type int } from "vreact/spec";
export function total(xs: readonly int[]): int {
  let s = 0;
  for (const x of xs) {
    s += x;
  }
  return s;
}
export function Sum() {
  const [xs, setXs] = useState<readonly int[]>([1, 2, 3]);
  return <button onClick={() => setXs([...xs, xs.length])}>{total(xs)}</button>;
}
