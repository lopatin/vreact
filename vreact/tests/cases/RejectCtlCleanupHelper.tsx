// expect: reject effect cleanups may not update state or call parent callbacks
// A setter reached through a local helper: the stale cleanup increments past 10.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlBump() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  const inc = () => { if (n < 10) setN((m) => m + 1); };
  useEffect(() => {
    return () => inc();
  });
  return <button onClick={() => inc()}>{n}</button>;
}
