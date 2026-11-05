// expect: fail index verdict=not-verified first=incomplete nextPos=incomplete inc=verified Counter=incomplete nextPos2=incomplete proved=4 failed=1 unchecked=3 errors=none why.nextPos=uses~first why.Counter=uses~first why.nextPos2=uses~first
// first's index obligation fails, so its (reducible) body holds an admitted `sorry`. The
// obligations below are TRUE (first([x + 1]) is x + 1), but their proofs unfold first and so
// use that sorry: they are blocked (not checked), neither proved nor failed. Before, they were
// reported FAILED ("the automation closed the goal with `sorry`"). Same in a component handler
// and in a module importing first; the independent inc stays verified.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { first } from "./model";
export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(first([n + 1]))}>{n}</button>;
}
