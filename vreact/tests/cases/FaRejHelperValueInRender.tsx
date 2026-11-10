// expect: reject state updates during render are not allowed
// Called for its value in the render, the helper does update state during render.
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
  const v = bump();
  return <button onClick={() => setN(v)}>{n}</button>;
}
