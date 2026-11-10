// expect: reject `a` is called again while it runs
// The same through handlers called as statements, starting from the later one's view: the
// recursive call is named (formerly "this call has no modelled effect: b()").
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const a = () => { if (n > 3) { b(); } };
  const b = () => { setN(0); a(); };
  return <button onClick={a}>{n}</button>;
}
