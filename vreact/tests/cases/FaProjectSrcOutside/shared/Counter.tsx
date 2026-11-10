import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < 3) setN(n + 1); }}>{n}</button>;
}
