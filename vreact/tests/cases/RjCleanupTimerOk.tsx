// expect: verified
// Accepted counterparts of RjRejectCleanupTdz: a cleanup returned from a branch clears only
// the timers registered on the path to its `return` (a handle exists once `const id = …`
// has run); the handle is never null there, so `if (id !== null)` is statically true.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjCleanupTimerOk(props: { readonly paused: boolean; readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.paused) return () => console.log("paused");
    const id = setInterval(() => setN((k) => k + 1), props.fast ? 100 : 1000);
    if (props.fast) {
      return () => {
        if (id !== null) clearInterval(id);
        console.log("fast");
      };
    }
    const t = setTimeout(() => setN((k) => k + 2), 50);
    return () => {
      clearInterval(id);
      clearTimeout(t);
    };
  }, [props.paused, props.fast]);
  return <p>{n}</p>;
}
