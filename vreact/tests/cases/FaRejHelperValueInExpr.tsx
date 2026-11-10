// expect: reject updates state or calls a parent callback: VTS inlines such a helper only where it is called as a statement
// The same helper with its value used inside an expression (`setN(bump())`) is rejected, and
// the message says why (it is not "during render").
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  const [log, setLog] = useState<int>(0);
  invariant(n >= 0 && log >= 0);
  const bump = (): int => {
    setLog((l) => l + 1);
    return n + 1;
  };
  return <button onClick={() => setN(bump())}>{n}</button>;
}
