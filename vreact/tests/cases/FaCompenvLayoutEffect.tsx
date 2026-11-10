// expect: reject useLayoutEffect is not modelled in VTS yet
// useLayoutEffect called as a statement at the top level, unconditionally: rejected because it is
// not modelled (its updates are synchronous, during the commit), not for a Rules of Hooks
// violation it does not have (the former message).
import { useState, useLayoutEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useLayoutEffect(() => {
    setN((p) => p + 1);
  }, []);
  return <button onClick={() => setN(0)}>{n}</button>;
}
