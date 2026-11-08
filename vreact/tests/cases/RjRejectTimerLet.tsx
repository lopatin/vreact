// expect: reject declare the timer handle with const
// A timer handle is bound by `const id = setTimeout(…)` (a `let` or `var` handle could be
// reassigned, and `var` is hoisted out of its temporal dead zone).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjTimerLet() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    let id = setTimeout(() => setN((k) => k + 1), 1000);
    return () => clearTimeout(id);
  }, []);
  return <p>{n}</p>;
}
