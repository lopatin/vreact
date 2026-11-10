// expect: status Pick=verified Pick2=verified App=verified
// The first argument of callbackRequires runs at every render, so it must be a read that
// cannot throw: `props.cb` on the props parameter (also parenthesized), or a callback
// destructured from the props parameter.
import { useState } from "react";
import { callbackRequires, type int } from "vreact/spec";

type PickProps = { readonly n: int; readonly onPick: (i: int) => void };

function Pick(props: PickProps) {
  callbackRequires(props.onPick, (i: int) => i >= 0);
  callbackRequires((props.onPick), (i: int) => i < props.n);
  return <button onClick={() => { if (0 < props.n) props.onPick(0); }}>{props.n}</button>;
}

function Pick2({ n, onPick: choose }: PickProps) {
  callbackRequires(choose, (i: int) => 0 <= i && i < n);
  return <button onClick={() => { if (0 < n) choose(n - 1); }}>{n}</button>;
}

export function App() {
  const [k, setK] = useState<int>(0);
  return (
    <div>
      <Pick n={3} onPick={(i: int) => setK(i)} />
      <Pick2 n={2} onPick={(i: int) => setK(i)} />
      <p>{k}</p>
    </div>
  );
}
