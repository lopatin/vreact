// expect: reject this invariant reads the state `b`, declared after it
// JS evaluates invariant(…)'s argument where it stands (vreact/spec's invariant is an ordinary
// call), so `forall` calls the predicate, which reads `b` in its temporal dead zone: a
// ReferenceError at mount. TypeScript reports a direct read (TS2448), not one inside the lambda.
// Formerly VERIFIED: the invariants were translated with every state value bound.
import { useState } from "react";
import { type int, invariant, forall } from "vreact/spec";

export function C() {
  const [a, setA] = useState<int>(0);
  invariant(a >= 0 && forall(0, 1, (i) => b >= i));
  const [b, setB] = useState<int>(0);
  return <button onClick={() => { setA(a + 1); setB(b + 1); }}>{a}{b}</button>;
}
