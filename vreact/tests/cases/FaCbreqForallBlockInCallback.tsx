// expect: verified
// Inside a callbackRequires lambda read as a contract, a forall/exists callback other than
// `(i) => condition` (a block body, a `function (k) { … }`) is read as code: the calls JS makes,
// as for an every/some callback.  The contract reading had rejected it ("quantifier body must be
// an expression"), although the base tool, which read the whole lambda as code, verified it.  The
// parent relies on the contract.
import { useState } from "react";
import { callbackRequires, exists, forall, invariant, type int } from "vreact/spec";

type CP = { readonly n: int; readonly onPick: (i: int) => void };
export function C(props: CP) {
  callbackRequires(props.onPick, (i) => i >= 0 && forall(0, props.n, (k) => { return k !== i + props.n; }));
  return <button onClick={() => props.onPick(0)}>c</button>;
}

type DP = { readonly onPick: (i: int) => void };
export function D(props: DP) {
  callbackRequires(props.onPick, (i) => exists(0, 3, function (k) { return k === i; }));
  return <button onClick={() => props.onPick(1)}>d</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <C n={3} onPick={(i) => setN(i)} />;
}
