// expect: verified
// React's hooks are recognised by their declaration: an import alias (`useState as useS`), a
// namespace import (`R.useState`) — and a local helper spelled like a hook is a local helper
// (formerly any callee spelled `useMemo` was React's useMemo): here it is inlined, x is 4, and
// the index below is in bounds.
import * as R from "react";
import { useState as useS } from "react";
import { type int, invariant } from "vreact/spec";

const NAMES: readonly string[] = ["a", "b", "c", "d", "e"];

export function RnHookAlias() {
  const [n, setN] = R.useState<int>(0);
  const [k, setK] = useS<int>(0);
  invariant(n >= 0 && k >= 0);
  const useMemo = (a: int, d: readonly int[]): int => a + d.length;
  const x = useMemo(3, [1]);
  return (
    <p onClick={() => { setN(n + 1); setK(k + 1); }}>
      {n} {NAMES[x]}
    </p>
  );
}
