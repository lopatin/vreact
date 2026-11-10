// expect: reject or as a name destructured from the props parameter
// The first argument of callbackRequires runs at every render: idiv(0, 0) throws
// "idiv by zero" on the first render of App (n = 0). Its divisor was never checked.
import { useState } from "react";
import { callbackRequires, idiv, type int } from "vreact/spec";

type PickProps = { readonly n: int; readonly onPick: (i: int) => void };

function Pick(props: PickProps) {
  callbackRequires([props][idiv(0, props.n)].onPick, (i: int) => i >= 0);
  return <button onClick={() => props.onPick(0)}>{props.n}</button>;
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
