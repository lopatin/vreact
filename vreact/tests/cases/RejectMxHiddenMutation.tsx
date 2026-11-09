// expect: reject in an expression
import { useState } from "react";
import { type int } from "vreact/spec";

// console arguments are not translated, but JS evaluates them: the state Map would change
export function App() {
  const [m, setM] = useState(new Map<int, int>());
  return <button onClick={() => { console.log(m.set(1, 2)); setM(new Map(m)); }}>{m.size}</button>;
}
