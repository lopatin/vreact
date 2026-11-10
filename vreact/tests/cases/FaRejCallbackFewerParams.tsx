// expect: verified
// A callback implementation may declare fewer parameters than the callback type (JS ignores
// the extra arguments, TypeScript accepts it): `onPick={() => setOpen(false)}` for
// `onPick: (i: int) => void` (formerly "callback expects 1 parameters"), also a local closure
// and a two-parameter callback implemented with one. The child's contract still holds for the
// arguments the implementation reads.
import { useState } from "react";
import { invariant, callbackRequires, type int } from "vreact/spec";

type CP = { readonly onPick: (i: int) => void; readonly onMove: (a: int, b: int) => void };
export function Child(props: CP) {
  callbackRequires(props.onMove, (a, b) => a >= 0 && b >= a);
  return (
    <div>
      <button onClick={() => props.onPick(1)}>x</button>
      <button onClick={() => props.onMove(2, 5)}>y</button>
    </div>
  );
}

export function App() {
  const [open, setOpen] = useState<boolean>(true);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const close = () => setOpen(false);
  return (
    <div>
      {open ? "o" : "c"}
      <Child onPick={() => setOpen(false)} onMove={(a) => setN(a)} />
      <Child onPick={close} onMove={() => setN(n + 1)} />
    </div>
  );
}
