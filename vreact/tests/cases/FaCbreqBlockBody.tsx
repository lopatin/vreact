// expect: verified
// A callbackRequires lambda with a block body is read as code (its obligations hold for every
// argument): still accepted, and the parent relies on it.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type CP = { readonly onPick: (i: int) => void };
export function C(props: CP) {
  callbackRequires(props.onPick, (i) => {
    const j = i + 1;
    return j > 0;
  });
  return <button onClick={() => props.onPick(0)}>c</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <C onPick={(i) => setN(i)} />;
}
