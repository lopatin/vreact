// expect: reject the dependency array cannot list it
// A useCallback function that reads a const declared after the call: the dependency array cannot
// list `step` (it is in its temporal dead zone there), so React keeps the function of the render
// where `n` last changed, with that render's `step`. Must not be translated with the current
// `step` (as a plain local handler is): rejected, with the reason.
import { useState, useCallback } from "react";
import { type int, invariant } from "vreact/spec";

export function C(props: { readonly up: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = useCallback(() => setN(n + step >= 0 ? n + step : n), [n]);
  const step: int = props.up ? 1 : -1;
  return <button onClick={bump}>{n}</button>;
}
