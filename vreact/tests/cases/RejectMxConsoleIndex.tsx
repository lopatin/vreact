// expect: reject a Map or Set has no indexed elements
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// console.log's argument clears the state Map through an element access: in JS the state object
// itself is emptied, behind React's back
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map([[1, 1]]));
  invariant(s.size === 1);
  return (
    <button
      onClick={() => {
        console.log((s as Map<int, int>)["clear"]());
        setS(new Map(s));
      }}
    >
      {s.size}
    </button>
  );
}
