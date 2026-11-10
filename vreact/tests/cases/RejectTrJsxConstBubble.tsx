// expect: reject event bubbling
// A JSX const is translated at its declaration; where it is placed is still checked.
import { useState } from "react";
export function TrJsxBubble() {
  const [n, setN] = useState(0);
  const btn = <button onClick={() => setN(n + 1)}>+</button>;
  return <div onClick={() => setN(0)}>{btn}</div>;
}
