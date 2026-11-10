// expect: fail effect-robust FaDepsEffectOuterFail=incomplete
// An effect that lists a top-level function (no dependency value: it never changes) is still
// checked: its update must keep the invariant from any state, and `inc(p) - 3` does not. Before,
// `[inc]` was refused ("functions are not first-class in VTS"), here and through `[bump]`.
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

function inc(p: int): int {
  return p + 1;
}

export function FaDepsEffectOuterFail() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = useCallback(() => setN((p) => inc(p) - 3), [inc]);
  useEffect(() => {
    bump();
  }, [bump, inc]);
  return <button type="button" onClick={() => setN(0)}>{n}</button>;
}
