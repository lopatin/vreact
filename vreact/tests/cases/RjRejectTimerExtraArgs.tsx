// expect: reject extra arguments of setTimeout are passed to its callback
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjTimerExtraArgs() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const id = setTimeout(() => setN((m) => m + 1), 10, n);
    return () => clearTimeout(id);
  }, [n]);
  return <p>{n}</p>;
}
