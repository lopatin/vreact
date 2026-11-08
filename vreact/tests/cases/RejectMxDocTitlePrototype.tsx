// expect: reject Set.prototype.clear is used without calling it directly
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

// the value assigned to document.title empties the state Set
export function C() {
  const [s, setS] = useState<ReadonlySet<int>>(new Set([1]));
  invariant(s.size === 1);
  return (
    <button
      onClick={() => {
        document.title = String(Set.prototype.clear.call(s));
        setS(new Set(s));
      }}
    >
      {s.size}
    </button>
  );
}
