// expect: reject which is reassigned after the function is created
// A handler closure reads a render-local `let` that is reassigned afterwards: in JS the
// click sees cap === 100 (closures capture the variable, not its value).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlRenderLet() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let cap: int = 5;
  const onSet = () => setN(cap);
  cap = 100;
  return <button onClick={onSet}>{n}</button>;
}
