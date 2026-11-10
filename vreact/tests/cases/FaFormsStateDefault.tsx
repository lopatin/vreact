// expect: reject a default value in the destructuring of useState(…) is not supported
// JS binds n to 5 whenever the state is undefined; the model bound n to the state slot (VERIFIED,
// yet the invariant fails at mount).
import { useState } from "react";
import { int, invariant } from "vreact/spec";

export function C() {
  const [n = 5, setN] = useState<int | undefined>(undefined);
  const [m, setM] = useState<int>(0);
  invariant(m >= 0 && n !== 5);
  return <button onClick={() => { setM(n === 5 ? -1 : 1); setN(undefined); }}>{m}</button>;
}
