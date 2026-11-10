// expect: fail handler
// The const declared after the handler is bound to its value, not to an arbitrary one: a step of
// -1 breaks the invariant, and the handler's obligation fails.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const dec = () => setN(n + step);
  const step: int = -1;
  return <button onClick={dec}>{n}</button>;
}
