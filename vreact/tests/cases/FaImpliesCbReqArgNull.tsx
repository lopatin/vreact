// expect: reject or as a name destructured from the props parameter
// callbackRequires(cb, pre) is a call: JS evaluates cb at every render (only pre is never
// called). Here n = 0 applies `!` to null, so the first render of App throws a TypeError;
// cb was never translated or checked, so this was VERIFIED.
import { useState } from "react";
import { callbackRequires, type int } from "vreact/spec";

type PickProps = { readonly n: int; readonly onPick: (i: int) => void };

function Pick(props: PickProps) {
  callbackRequires((props.n > 0 ? props : null)!.onPick, (i: int) => i >= 0 && i < props.n);
  return <button onClick={() => { if (0 < props.n) props.onPick(0); }}>{props.n}</button>;
}

export function App() {
  const [k, setK] = useState<int>(0);
  return (
    <div>
      <Pick n={0} onPick={(i: int) => setK(i)} />
      <p>{k}</p>
    </div>
  );
}
