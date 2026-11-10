// expect: reject or as a name destructured from the props parameter
// Any expression ending in `.onPick` was taken for the callback prop: here JS reads
// `.onPick` of undefined at every render and throws a TypeError.
import { useState } from "react";
import { callbackRequires, type int } from "vreact/spec";

type PickProps = { readonly n: int; readonly onPick: (i: int) => void };

function Pick(props: PickProps) {
  callbackRequires((undefined as unknown as PickProps).onPick, (i: int) => i >= 0 && i < props.n);
  return <button onClick={() => { if (0 < props.n) props.onPick(0); }}>{props.n}</button>;
}

export function App() {
  const [k, setK] = useState<int>(0);
  return (
    <div>
      <Pick n={3} onPick={(i: int) => setK(i)} />
      <p>{k}</p>
    </div>
  );
}
