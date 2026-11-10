// expect: reject is a const of the effect body that VTS cannot bind in a timer callback: its value has proof obligations of its own
// An effect-local const whose value has obligations (here the divisor, proved in the effect body
// from the precondition) is not translated again in the timer callback: rejected with that
// reason.
import { useState, useEffect } from "react";
import { invariant, requires, type int } from "vreact/spec";

export function C(props: { readonly d: int }) {
  requires(props.d > 0);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const r: int = 100 % props.d;
    const id = setTimeout(() => setN(r), 100);
    return () => clearTimeout(id);
  }, [props.d]);
  return <p>{n}</p>;
}
