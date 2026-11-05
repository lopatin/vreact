// expect: fail props-stability
// State survives a re-render with new props: an invariant tying state to a prop breaks
// when the parent lowers `max`.
import { useState } from "react";
import { requires, invariant, type int } from "vreact/spec";
export function PropsStability(props: { readonly max: int }) {
  requires(props.max > 0);
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= props.max);
  return <button onClick={() => { if (n < props.max) setN(n + 1); }}>{n}</button>;
}
