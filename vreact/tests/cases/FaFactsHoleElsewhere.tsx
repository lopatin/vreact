// expect: fail handler init-invariant
// A hole() that the failing goal does not unfold to (in the rendered text, in a handler)
// leaves a genuine failure failed: C's decrement breaks the invariant, and so does D's
// initial state.
import { useState } from "react";
import { invariant, hole, type int } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n - 1)}>{hole<string>()}</button>;
}

export function D() {
  const [n, setN] = useState<int>(-1);
  invariant(n >= 0);
  return <button onClick={() => setN(hole<int>())}>{n}</button>;
}
