// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { useState } from "react";
import { type int } from "vreact/spec";

// the Map handed to React is mutated afterwards
export function App() {
  const [m, setM] = useState<ReadonlyMap<int, int>>(new Map());
  return (
    <button onClick={() => {
      const n = new Map(m);
      setM(n);
      n.set(1, 2);
    }}>{m.size}</button>
  );
}
