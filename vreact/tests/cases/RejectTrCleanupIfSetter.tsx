// expect: reject effect cleanups may not update state or call parent callbacks
// if/else in a cleanup is allowed, but its branches obey the cleanup rule.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function TrCleanupSet() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  useEffect(() => {
    const id = setTimeout(() => setN(1), 10);
    return () => {
      if (n > 5) clearTimeout(id);
      else setN(n + 1);
    };
  }, [n]);
  return <p>{n}</p>;
}
