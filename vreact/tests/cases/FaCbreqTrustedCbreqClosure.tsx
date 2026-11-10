// expect: reject which is reassigned after the function is created
// The callbackRequires of a @trusted component is translated (the contract its parent's
// handler may assume), so closures in it must agree with JS.  In JS the lambda is true for
// every i (f reads the latest y, 2); the translation would read y as 1 and make the contract
// False, so App's handler, which sets n = 1 against n === 0, would hold vacuously.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type CP = { readonly onPick: (i: int) => void };

/** @trusted */
export function C(props: CP) {
  callbackRequires(props.onPick, (i) => {
    let y = 1;
    const f = () => y;
    y = 2;
    return f() === 2;
  });
  return <button onClick={() => props.onPick(1)}>c</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n === 0);
  return <C onPick={(i) => setN(i)} />;
}
