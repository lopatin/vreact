// expect: reject event bubbling
import { useState } from "react";
export function Bad() {
  const [n, setN] = useState(0);
  return (
    <div onClick={() => setN(0)}>
      <button onClick={() => setN(n + 1)}>+</button>
    </div>
  );
}
