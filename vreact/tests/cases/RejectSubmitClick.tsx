// expect: reject one click runs both handlers
import { useState } from "react";
export function Bad() {
  const [n, setN] = useState(0);
  return (
    <form onSubmit={(e) => { e.preventDefault(); setN(0); }}>
      <button onClick={() => setN(n + 1)}>go</button>
    </form>
  );
}
