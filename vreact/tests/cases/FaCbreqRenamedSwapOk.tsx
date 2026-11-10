// expect: verified
// The contract stated on the local `onA` of `{ onA: onB, onB: onA }` is props.onB's: the child's
// call onA(1) (props.onB(1)) keeps it, and the parent's onB handler relies on it (n >= 0). The
// contract used to land on props.onA, leaving the parent's onB handler unprovable.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type CP = { readonly onA: (i: int) => void; readonly onB: (i: int) => void };
export function C({ onA: onB, onB: onA }: CP) {
  callbackRequires(onA, (i) => i >= 0);
  return <button onClick={() => onA(1)}>c</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <C onA={(i) => setN(0)} onB={(i) => setN(i)} />;
}
