// expect: verified
// A callbackRequires lambda is never run by JS: it is a contract, so implies(a, b) is an
// implication whose consequent is translated under its guard, as in requires/invariant. The
// index props.xs[i] is in bounds there (it used to be read as code, with an unguarded index
// obligation that failed). The parent relies on an implies contract.
import { useState } from "react";
import { callbackRequires, implies, invariant, type int } from "vreact/spec";

type CP = { readonly xs: readonly int[]; readonly onPick: (i: int) => void };
export function C(props: CP) {
  callbackRequires(props.onPick, (i) => implies(0 <= i && i < props.xs.length, props.xs[i] >= 0));
  return <button onClick={() => props.onPick(-1)}>c</button>;
}

type DP = { readonly strict: boolean; readonly onSet: (v: int) => void };
export function D(props: DP) {
  callbackRequires(props.onSet, (v) => implies(props.strict, v >= 0));
  return <button onClick={() => props.onSet(props.strict ? 3 : -3)}>d</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <D strict={true} onSet={(v) => setN(v)} />;
}
