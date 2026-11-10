// expect: reject is declared outside this function
import { useState } from "react";
import { type int } from "vreact/spec";

// the handler mutates a render-time Map shared by every click
export function App() {
  const [c, setC] = useState(0);
  const seen = new Set<int>();
  return <button onClick={() => { seen.add(c); setC(seen.size); }}>{c}</button>;
}
