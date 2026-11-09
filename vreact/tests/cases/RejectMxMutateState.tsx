// expect: reject is not a local variable of this function
import { useState } from "react";
import { type int } from "vreact/spec";

// mutating a state Map in place: React keeps the same object (no re-render), the model a new value
export function Counts() {
  const [m, setM] = useState(new Map<string, int>());
  return <button onClick={() => { m.set("a", 1); setM(m); }}>{m.size}</button>;
}
