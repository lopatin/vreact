// expect: verified
// Forwarding a child's one-parameter callback to a grandchild slot of two parameters: the
// grandchild's calls pass two arguments to the parent's function, which reads the first
// (formerly "callback arity mismatch forwarding onPick"). The grandchild's contract on (a, b)
// gives the child's on a.
import { useState } from "react";
import { invariant, callbackRequires, type int } from "vreact/spec";
type GCProps = { readonly onX: (a: int, b: int) => void };
export function GC(props: GCProps) {
  callbackRequires(props.onX, (a, b) => a >= 0);
  return <button onClick={() => props.onX(5, -1)}>x</button>;
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
