// expect: fail precondition
// React renders nothing for a boolean child, but JavaScript evaluates it: the
// precondition of perItem (n !== 0) must be checked; after the click n = 0.
import { useState } from "react";
import { invariant, requires, idiv, type int } from "vreact/spec";
function perItem(total: int, n: int): int {
  requires(n !== 0);
  return idiv(total, n);
}
export function App() {
  const [n, setN] = useState<int>(1);
  invariant(n >= 0);
  return (
    <div>
      <p>{perItem(100, n) > 10}</p>
      <button onClick={() => setN(0)}>clear</button>
    </div>
  );
}
