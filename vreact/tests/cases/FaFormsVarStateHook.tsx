// expect: reject declare the result of useState(…) with const, not var
// A `var` state hook is one hoisted binding: the second declaration rebinds setN, so f (created
// before it) calls m's setter at the click and breaks m's invariant. Was VERIFIED (compenv fix).
import { useState } from "react";
import { int, invariant } from "vreact/spec";

export function C() {
  var [n, setN] = useState<int>(0);
  const f = () => setN(-1);
  var [m, setN] = useState<int>(0);
  invariant(m >= 0);
  return <button onClick={f}>{n}{m}</button>;
}
