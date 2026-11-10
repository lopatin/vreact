// expect: fail callback
// The implies contract gives the parent v >= 0 only when strict: with strict={false} the onSet
// handler cannot keep n >= 0.
import { useState } from "react";
import { callbackRequires, implies, invariant, type int } from "vreact/spec";

type DP = { readonly strict: boolean; readonly onSet: (v: int) => void };
export function D(props: DP) {
  callbackRequires(props.onSet, (v) => implies(props.strict, v >= 0));
  return <button onClick={() => props.onSet(props.strict ? 3 : -3)}>d</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <D strict={false} onSet={(v) => setN(v)} />;
}
