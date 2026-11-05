// expect: reject both run on one native "click" event
// React's ChangeEventPlugin fires a checkbox's onChange from the native click:
// one click runs onClick and onChange in one batch, both from the same snapshot.
import { useState } from "react";
import { invariant } from "vreact/spec";
export function Bad() {
  const [a, setA] = useState(false);
  const [b, setB] = useState(false);
  invariant(!(a && b));
  return <input type="checkbox" checked={a} onClick={() => { if (!b) setA(true); }} onChange={() => { if (!a) setB(true); }} />;
}
