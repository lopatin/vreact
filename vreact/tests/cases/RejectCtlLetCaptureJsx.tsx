// expect: reject which is reassigned after the function is created
// The handler inside a JSX constant runs after render, when cap === 100.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlJsxLet() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let cap: int = 5;
  const btn = <button onClick={() => setN(cap)}>{n}</button>;
  cap = 100;
  return <div>{btn}<span>{cap}</span></div>;
}
