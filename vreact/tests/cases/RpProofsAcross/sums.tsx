// The lemma also helps this module's own components (View.lean imports Proofs.sums).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
/** @opaque */
export function total(xs: readonly int[]): int {
  return xs.reduce((a, b) => a + b, 0);
}
export function Totals() {
  const [xs, setXs] = useState<readonly int[]>([]);
  invariant(total(xs.concat(xs)) === 2 * total(xs));
  return <button onClick={() => setXs(xs.concat([1]))}>{total(xs)}</button>;
}
