// expect: status verdict=incomplete inc=incomplete Counter=incomplete Counter.certificate=incomplete why.inc=sorryAx why.Counter=sorryAx errors=none
// The axiom check covers the user proofs too (R4 item 12): proofs/m.lean's lemma `bad` is
// false and admitted with `sorry` (allowed syntax: it is an axiom, `sorryAx`, that the report
// shows). inc's false ensures is "proved" with it, and Counter's handler uses that contract of
// the @opaque inc: neither inc, Counter nor the app certificate may be VERIFIED.
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
/** @opaque */
export function inc(x: int): int {
  ensures((r: int) => r === x + 2);
  return x + 1;
}
export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n % 2 === 0);
  return <button onClick={() => setN(inc(n))}>{n}</button>;
}
