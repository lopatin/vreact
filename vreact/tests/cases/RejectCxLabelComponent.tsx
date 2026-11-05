// expect: reject <Row> is nested inside a <label>
// The label re-dispatches clicks on Row's non-interactive content to its control, which
// may be inside Row: Row's span onClick and checkbox onChange (fine on their own) would
// run in one batch.  Row is checked alone, so the label is rejected here.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Row() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <input type="checkbox" checked={n > 0} onChange={() => { if (n < 1) setN((m) => m + 1); }} />
      <span onClick={() => { if (n < 1) setN((m) => m + 1); }}>agree</span>
    </div>
  );
}
export function A() {
  return (
    <label>
      <Row />
    </label>
  );
}
