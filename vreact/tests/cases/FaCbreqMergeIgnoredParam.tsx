// expect: verified
// Several callbackRequires for one callback are conjoined, also when an earlier one ignores a
// parameter a later one names (it used to leave a placeholder `_` in the conjunction: an
// internal Lean error). The parent relies on every conjunct.
import { useState } from "react";
import { type int, callbackRequires, invariant } from "vreact/spec";

type P = { onPair: (a: int, b: int) => void; onTri: (a: int, b: int, c: int) => void };

export function Child(props: P) {
  callbackRequires(props.onPair, (a) => a > 0);
  callbackRequires(props.onPair, (x, y) => y > 0);
  callbackRequires(props.onTri, (y) => y > 0);
  callbackRequires(props.onTri, (x, y, z) => x + y > 1 && z > 0);
  return (
    <div>
      <button onClick={() => props.onPair(1, 2)}>a</button>
      <button onClick={() => props.onTri(1, 1, 1)}>b</button>
    </div>
  );
}

export function Parent() {
  const [v, setV] = useState<int>(1);
  invariant(v > 0);
  return <Child onPair={(a, b) => setV(a + b)} onTri={(a, b, c) => setV(a + b + c)} />;
}
