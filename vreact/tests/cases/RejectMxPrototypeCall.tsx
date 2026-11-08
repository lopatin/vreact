// expect: reject Map.prototype.set is used without calling it directly
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// Map.prototype.set.call(s, …) fills the state Map itself
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map());
  invariant(s.size === 0);
  return (
    <button
      onClick={() => {
        console.log(Map.prototype.set.call(s, 1, 1));
        setS(s);
      }}
    >
      {s.size}
    </button>
  );
}
