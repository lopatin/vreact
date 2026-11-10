// expect: reject two children of <div> have the same key "x"
// React reconciles the static children of an element as one array: two of them with the same
// key make reconcileChildrenArray keep one old fiber per key, and the other is never deleted
// (its DOM stays, with stale handlers).  Equal written keys on siblings that are always present
// are rejected (jsx-r1-3, effects-r1-1, lean-r1-1).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Two() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>+</button>
      <p key="x">one</p>
      <p key={"x"}>two</p>
    </div>
  );
}
