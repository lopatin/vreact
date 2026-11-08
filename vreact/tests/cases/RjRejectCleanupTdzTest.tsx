// expect: reject before `const id = setInterval(…)` has run on this path
// The same through a test of the handle: `id !== null` reads `id` too (in its temporal dead
// zone on the paused path), so it is not statically true there.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjCleanupTdzTest(props: { readonly paused: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.paused) {
      return () => {
        if (id !== null) clearInterval(id);
      };
    }
    const id = setInterval(() => setN((k) => k + 1), 1000);
    return () => clearInterval(id);
  }, [props.paused]);
  return <p>{n}</p>;
}
