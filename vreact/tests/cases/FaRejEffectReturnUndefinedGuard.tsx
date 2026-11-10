// expect: fail effect-robust
// The guard of `return undefined;` is the timer's only reason for `props.step >= 0`; without
// it (here the early return tests something else) the timer may make `n` negative.
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

export function G(props: { readonly step: int; readonly on: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (!props.on) return undefined;
    const id = setTimeout(() => setN((m) => m + props.step), 10);
    return () => clearTimeout(id);
  }, [props.step, props.on]);
  return <p>{n}</p>;
}
