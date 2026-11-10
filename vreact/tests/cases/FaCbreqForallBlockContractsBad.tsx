// expect: fail precondition handler
// A block-bodied forall in a requires, and a `function` exists in an invariant (read as code),
// are still checked: count(3) breaks the precondition (2 is not below 2), and the handler's 0
// leaves exists(0, 0, …) false.
import { useState } from "react";
import { requires, invariant, forall, exists, type int } from "vreact/spec";

export function count(n: int): int {
  requires(forall(0, n, (i) => { return i < 2; }));
  return n;
}

export const THREE: int = count(3);

export function List() {
  const [n, setN] = useState<int>(1);
  invariant(exists(0, n, function (k) { return k === 0; }));
  return <button onClick={() => setN(0)}>{n}</button>;
}
