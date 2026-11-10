// expect: reject not inside a callback that VTS translates as a value, such as an array method's
// The same in an onClick handler.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function B() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => { console.log([5].map((x) => { setN(x); return x; })); }}>{n}</button>;
}
