// expect: verified
// An invariant between two useStates that reads (also inside a lambda) only the state declared
// before it: accepted.
import { useState } from "react";
import { type int, invariant, forall } from "vreact/spec";

export function C() {
  const [a, setA] = useState<int>(0);
  invariant(forall(0, 1, (i) => a >= i));
  const [b, setB] = useState<int>(0);
  invariant(b >= 0);
  return <button onClick={() => { setA(a + 1); setB(b + 1); }}>{a}{b}</button>;
}
