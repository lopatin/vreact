// expect: verified
// callbackRequires on a renamed destructured callback prop: `pick` holds props.onPick, so the
// contract is onPick's (it used to be rejected with "callbackRequires expects a callback prop").
// The parent relies on it.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type CP = { readonly onPick: (i: int) => void };
export function C({ onPick: pick }: CP) {
  callbackRequires(pick, (i) => i >= 0);
  return <button onClick={() => pick(1)}>c</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <C onPick={(i) => setN(i)} />;
}
