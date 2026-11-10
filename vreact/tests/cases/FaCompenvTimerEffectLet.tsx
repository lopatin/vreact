// expect: reject `step` is a `let` of the effect body: VTS binds in a timer callback only
// A `let` of the effect body is not bound in a timer callback (its value depends on the
// assignments before the registration): rejected with that reason, not "unknown identifier".
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function C(props: { readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    let step: int = 1;
    if (props.fast) step = 2;
    const id = setInterval(() => setN((k) => k + step), 100);
    return () => clearInterval(id);
  }, [props.fast]);
  return <p>{n}</p>;
}
