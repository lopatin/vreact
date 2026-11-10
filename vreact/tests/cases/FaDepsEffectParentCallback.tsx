// expect: reject `props.onPick` is a parent callback: it cannot be an effect dependency
// A parent callback in an effect's dependencies: an effect never calls one, and when the parent
// passes a new function is not modelled. Rejected with that reason (before: "props.onPick is a
// callback: it can only be called in a handler or passed to a child").
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsEffectParentCallback(props: { readonly onPick: (x: int) => void }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => { setN((p) => p + 1); }, [props.onPick]);
  return <button type="button" onClick={() => props.onPick(n)}>{n}</button>;
}
