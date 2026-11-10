// expect: fail callback-contract
// The grandchild promises only b >= 0, and calls onX(-5, 1): forwarded, the parent's function
// would set n to -5. The forwarded callback's contract (i >= 0 on the first argument) fails.
import { useState } from "react";
import { invariant, callbackRequires, type int } from "vreact/spec";
type GCProps = { readonly onX: (a: int, b: int) => void };
export function GC(props: GCProps) {
  callbackRequires(props.onX, (a, b) => b >= 0);
  return <button onClick={() => props.onX(-5, 1)}>x</button>;
}
type ChildProps = { readonly onPick: (i: int) => void };
export function Child(props: ChildProps) {
  callbackRequires(props.onPick, (i) => i >= 0);
  return <GC onX={props.onPick} />;
}
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <div><p>{n}</p><Child onPick={(i) => setN(i)} /></div>;
}
