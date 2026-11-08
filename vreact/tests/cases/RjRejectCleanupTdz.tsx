// expect: reject before `const id = setTimeout(…)` has run on this path
// When `paused` is true the effect returns its cleanup before `const id = …` runs: React
// calls that cleanup on unmount (or when `paused` changes), and reading `id` in its temporal
// dead zone throws a ReferenceError (TypeScript does not flag a use inside a closure).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjCleanupTdz(props: { readonly paused: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.paused) return () => clearTimeout(id);
    const id = setTimeout(() => setN((k) => k + 1), 1000);
    return () => clearTimeout(id);
  }, [props.paused]);
  return <p>{n}</p>;
}
