// expect: verified
// The fix for PropsStability: keep the invariant prop-independent, clamp when rendering.
import { useState } from "react";
import { requires, invariant, type int } from "vreact/spec";
export function ClampedCounter(props: { readonly max: int }) {
  requires(props.max > 0);
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  const shown = Math.min(n, props.max);
  return <button disabled={n >= props.max} onClick={() => { if (n < props.max) setN(n + 1); }}>{shown}</button>;
}
