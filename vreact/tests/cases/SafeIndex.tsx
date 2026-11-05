// expect: verified
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function SafeIndex() {
  const [xs] = useState<readonly string[]>(["a", "b", "c"]);
  const [i, setI] = useState<int>(0);
  invariant(xs.length === 3 && 0 <= i && i < xs.length);
  return <button onClick={() => setI(i + 1 < xs.length ? i + 1 : 0)}>{xs[i]}</button>;
}
