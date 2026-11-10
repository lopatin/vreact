// expect: reject type assertions (`as`) are not allowed in VTS
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// through an `any` cast the receiver is no longer typed Map: console.log's arguments are checked
// like any other VTS expression
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map([[1, 1]]));
  invariant(s.size === 1);
  return (
    <button
      onClick={() => {
        localStorage.setItem("x", String((s as any).clear()));
        setS(new Map(s));
      }}
    >
      {s.size}
    </button>
  );
}
