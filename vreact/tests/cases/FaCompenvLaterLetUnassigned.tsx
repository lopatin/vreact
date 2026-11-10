// expect: verified
// A handler may read a `let` declared after it that nothing assigns: it has one value from its
// initialisation on (formerly rejected as "unknown identifier `step`").
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const inc = () => setN(n + step);
  let step: int = 2;
  return <button onClick={inc}>{n}</button>;
}
