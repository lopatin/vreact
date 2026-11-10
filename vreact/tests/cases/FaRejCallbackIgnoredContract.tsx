// expect: fail callback
// An implementation that ignores the argument gets no fact from the child's contract about
// what it does not read: here the handler sets n to -1 whatever the child passes.
import { useState } from "react";
import { invariant, callbackRequires, type int } from "vreact/spec";
type CP = { readonly onPick: (i: int) => void };
export function Child(props: CP) {
  callbackRequires(props.onPick, (i) => i >= 0);
  return <button onClick={() => props.onPick(1)}>x</button>;
}
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <div>{n}<Child onPick={() => setN(-1)} /></div>;
}
