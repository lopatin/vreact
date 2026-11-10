// expect: fail nonzero-divisor
// `useState(10 % a)` is evaluated at every render (its value used only at mount): after the click
// sets a to 0, JS evaluates 10 % 0 there. The initial value is also checked in the render, with
// that render's state, and its obligation fails (the lazy form in FaCompenvInitReadsState runs at
// mount only and verifies).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function C() {
  const [a, setA] = useState<int>(5);
  const [b] = useState<int>(10 % a);
  invariant(b === 0);
  return <button onClick={() => setA(0)}>{a}{b}</button>;
}
