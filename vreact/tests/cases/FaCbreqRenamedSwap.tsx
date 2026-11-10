// expect: fail callback-contract faildesc=through~the~local~onA
// callbackRequires names its callback by the binding it holds, not by its spelling: with
// `{ onA: onB, onB: onA }` the local `onA` holds props.onB, so the contract below is props.onB's,
// and the call onA(-7) (props.onB(-7) in JS) breaks it. It used to be attached to props.onA (the
// prop spelled like the local) and the component was VERIFIED with an app certificate.
import { useState } from "react";
import { type int, callbackRequires, invariant } from "vreact/spec";

type P = { onA: (x: int) => void; onB: (x: int) => void };

export function Child({ onA: onB, onB: onA }: P) {
  callbackRequires(onA, (x) => x > 0);
  return <button onClick={() => onA(-7)}>a</button>;
}

export function Parent() {
  const [v, setV] = useState<int>(1);
  invariant(v !== 0);
  return <Child onA={(x) => setV(1)} onB={(x) => setV(1)} />;
}
