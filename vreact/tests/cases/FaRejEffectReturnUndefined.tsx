// expect: verified
// `return undefined;` (and `return void 0;`) in an effect is `return;`: React calls an effect's
// result as its cleanup only when it is not undefined (formerly rejected as "an effect cleanup
// must be an inline function"); likewise in an event handler. A timer keeps the guard of such
// an early return: `props.step >= 0` holds when G's timer runs, which keeps `n` non-negative.
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

export function B(props: { readonly on: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (!props.on) return undefined;
    const id = setInterval(() => setN((m) => m + 1), 5);
    return () => clearInterval(id);
  }, [props.on]);
  return <p>{n}</p>;
}

export function G(props: { readonly step: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.step < 0) return void 0;
    // (the guard `props.step >= 0` is what keeps n non-negative)
    const id = setTimeout(() => setN((m) => m + props.step), 10);
    return () => clearTimeout(id);
  }, [props.step]);
  return <button onClick={() => { if (n > 100) return undefined; setN(n + 1); }}>{n}</button>;
}
