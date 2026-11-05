// expect: verified
// The guarded form: the boolean child's obligation holds under `n !== 0 &&`.
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
      <p>{n !== 0 && perItem(100, n) > 10}</p>
      <p>{n > 5}</p>
      <button onClick={() => setN(0)}>clear</button>
    </div>
  );
}
