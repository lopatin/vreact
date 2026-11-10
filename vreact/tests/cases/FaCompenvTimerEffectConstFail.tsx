// expect: fail effect-robust
// The effect-local const is bound to its value in the timer callback: a negative step breaks the
// invariant (with an arbitrary value, or none, this could not be told apart from the positive
// one).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function Ticker(props: { readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const step: int = props.fast ? -2 : 1;
    const id = setInterval(() => setN((k) => k + step), 100);
    return () => clearInterval(id);
  }, [props.fast]);
  return <p>{n}</p>;
}
