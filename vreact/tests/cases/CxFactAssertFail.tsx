// expect: fail assert
// The assertion is not provable (n may be 5), and it is reported; the handler's
// invariant preservation uses the asserted fact (proved separately), so it is not
// reported as well.
import { useState } from "react";
import { assert, invariant, type int } from "vreact/spec";
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n <= 5);
  return <button onClick={() => { assert(n < 5); setN(n + 1); }}>{n}</button>;
}
