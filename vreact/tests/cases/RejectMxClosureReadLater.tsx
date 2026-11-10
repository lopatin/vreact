// expect: reject which is mutated after the function is created
import { useState } from "react";
import { type int } from "vreact/spec";

// the handler sees the Map as it is when it runs (after the set below)
export function App() {
  const [c, setC] = useState(0);
  const n = new Map<int, int>();
  const show = () => setC(n.size);
  n.set(1, 1);
  return <button onClick={show}>{c}</button>;
}
