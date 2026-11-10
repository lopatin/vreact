// expect: reject Rules of Hooks
// useMemo outside rendering throws after setA was queued: setB never runs (a !== b).
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlPair() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a === b);
  return (
    <button
      onClick={() => {
        setA((x) => x + 1);
        const step = useMemo(() => 1, []);
        setB((y) => y + step);
      }}
    >
      {a}/{b}
    </button>
  );
}
