// expect: fail handler init-invariant props-stability root-precondition failtext=timeout failed=5 unchecked=0 errors=none verdict=not-verified Steps=incomplete
// vreact.json gives every obligation a budget far too small to finish. Each obligation must
// fail on its own (a timeout reported at that obligation), the obligations after the first
// timeout in `render` must still run (before: one shared budget per declaration, the first
// timeout aborted `render`, later obligations were counted as proved and the error was blamed
// on an unrelated obligation or filed as an internal error).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Steps() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  return (
    <div>
      <button onClick={() => setN(n < 10 ? n + 1 : n)}>+1</button>
      <button onClick={() => setN(n > 0 ? n - 1 : n)}>-1</button>
    </div>
  );
}
