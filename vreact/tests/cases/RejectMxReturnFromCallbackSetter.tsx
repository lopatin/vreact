// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// the click stores (through a callback's return) the same Map that it fills afterwards: React
// keeps the filled object, so the invariant breaks
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map());
  invariant(s.size === 0);
  return (
    <button
      onClick={() => {
        const n = new Map<int, int>();
        const arr = [0].map((x) => {
          return n;
        });
        setS(arr[0]);
        n.set(1, 1);
      }}
    >
      {s.size}
    </button>
  );
}
